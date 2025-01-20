open Fleche
open Petanque
open Annotated_ast_node
open Vernacexpr
open Proof_tree

type proof = {
  proposition : annotatedASTNode;
  proof_steps : annotatedASTNode list;
}
(* proposition can also be a type, better name ? *)

(* A node can have multiple names (ie mutual recursive defs) *)
let get_names (node : annotatedASTNode) : string list =
  match node.ast.ast_info with
  | Some infos ->
      List.concat_map
        (fun (info : Lang.Ast.Info.t) ->
          match info.name.v with None -> [] | Some s -> [ s ])
        infos
  | None -> []

let get_proof_name (p : proof) : string option =
  List.nth_opt (get_names p.proposition) 0

let get_tree_name (Node (x, children)) : string option =
  List.nth_opt (get_names x) 0

let doc_node_to_string (d : Doc.Node.Ast.t) : string =
  let pp_expr = Ppvernac.pr_vernac_expr (Coq.Ast.to_coq d.v).CAst.v.expr in
  Pp.string_of_ppcmds pp_expr

let proof_to_coq_script_string (p : proof) : string =
  doc_node_to_string p.proposition.ast
  ^ "\n"
  ^ String.concat "\n"
      (List.map (fun n -> doc_node_to_string n.ast) p.proof_steps)

let get_proof_state (start_result : Agent.State.t Agent.Run_result.t Agent.R.t)
    : Agent.State.t =
  match start_result with
  | Ok run_result -> run_result.st
  | Error err ->
      Printf.eprintf "Error: %s\n" (Agent.Error.to_string err);
      raise (Failure "Failed to start proof")

let count_goals (token : Coq.Limits.Token.t) (st : Agent.State.t) : int =
  let goals = Agent.goals ~token ~st in
  match goals with
  | Ok (Some reified_goals) -> List.length reified_goals.goals
  | Ok None -> 0
  | Error _ -> 0

let rec print_tree (tree : annotatedASTNode nary_tree) (indent : string) : unit
    =
  match tree with
  | Node (value, children) ->
      Printf.printf "%sNode(%s)\n" indent value.repr;
      List.iter (fun child -> print_tree child (indent ^ "  ")) children

let rec proof_steps_with_goalcount (token : Coq.Limits.Token.t)
    (st : Agent.State.t) (steps : annotatedASTNode list) :
    (annotatedASTNode * int) list =
  match steps with
  | [] -> []
  | step :: tail ->
      let state = Agent.run ~token ~st ~tac:step.repr () in
      let agent_state = get_proof_state state in
      let goal_count = count_goals token agent_state in
      (step, goal_count) :: proof_steps_with_goalcount token agent_state tail

let print_parents
    (parents : (int * annotatedASTNode, int * annotatedASTNode) Hashtbl.t) :
    unit =
  Hashtbl.iter
    (fun (k_idx, k_tactic) (v_idx, v_tactic) ->
      Printf.printf
        "Parent: (idx: %d, tactic: %s) -> Child: (idx: %d, tactic: %s)\n" k_idx
        k_tactic.repr v_idx v_tactic.repr)
    parents

type parent_category = Fork | Linear

let rec pop_until_fork
    (prev_pars : (int * annotatedASTNode * parent_category) list) :
    (int * annotatedASTNode * parent_category) list =
  match prev_pars with
  | [] -> []
  | (_, _, cat_par) :: tail_par -> (
      match cat_par with Fork -> prev_pars | Linear -> pop_until_fork tail_par)

let rec get_parents_rec (steps_with_goals : (annotatedASTNode * int) list)
    (prev_goals : int)
    (prev_pars : (int * annotatedASTNode * parent_category) list) (idx : int)
    (parents : (int * annotatedASTNode, int * annotatedASTNode) Hashtbl.t) =
  match steps_with_goals with
  | [] -> parents
  | (step, new_goals) :: tail -> (
      match prev_pars with
      | [] ->
          if new_goals > prev_goals then
            get_parents_rec tail new_goals
              [ (idx, step, Fork) ]
              (idx + 1) parents
          else
            get_parents_rec tail new_goals
              [ (idx, step, Linear) ]
              (idx + 1) parents
      | (idx_par, tactic_par, _) :: _ ->
          let par = (idx_par, tactic_par) in
          if new_goals < prev_goals then (
            Hashtbl.add parents par (idx, step);
            if new_goals > 0 then
              get_parents_rec tail new_goals (pop_until_fork prev_pars)
                (idx + 1) parents
            else
              get_parents_rec tail new_goals
                [ (idx, step, Linear) ]
                (idx + 1) parents)
          else if new_goals = prev_goals then (
            Hashtbl.add parents par (idx, step);
            get_parents_rec tail new_goals
              ((idx, step, Linear) :: prev_pars)
              (idx + 1) parents)
          else (
            Hashtbl.add parents par (idx, step);
            get_parents_rec tail new_goals
              ((idx, step, Fork) :: prev_pars)
              (idx + 1) parents))

let rec proof_tree_from_parents (cur_node : int * annotatedASTNode)
    (parents : (int * annotatedASTNode, int * annotatedASTNode) Hashtbl.t) :
    annotatedASTNode nary_tree =
  let _, tactic = cur_node in

  let childs = Hashtbl.find_all parents cur_node in
  Node
    ( tactic,
      List.rev_map (fun node -> proof_tree_from_parents node parents) childs )

let get_init_state (doc : Doc.t) (p : proof) :
    Agent.State.t Agent.Run_result.t Agent.R.t option =
  match get_proof_name p with
  | Some name ->
      let token = Coq.Limits.Token.create () in
      Some (Agent.start ~token ~doc ~thm:name ())
  | None -> None

let treeify_proof (doc : Doc.t) (p : proof) : annotatedASTNode nary_tree =
  let token = Coq.Limits.Token.create () in
  let init_state = Option.get (get_init_state doc p) in
  let proof_state = get_proof_state init_state in
  let steps_with_goals =
    proof_steps_with_goalcount token proof_state p.proof_steps
  in

  let parents = Hashtbl.create (List.length steps_with_goals) in

  let _ = get_parents_rec steps_with_goals 1 [] 0 parents in
  Node
    ( p.proposition,
      [ proof_tree_from_parents (0, List.hd p.proof_steps) parents ] )

let rec proof_tree_to_node_list (Node (value, children)) : annotatedASTNode list
    =
  value :: List.concat (List.map proof_tree_to_node_list children)

let tree_to_proof (tree : annotatedASTNode nary_tree) : proof =
  let nodes = proof_tree_to_node_list tree in
  { proposition = List.hd nodes; proof_steps = List.tl nodes }

let previous_steps_from_tree (node : annotatedASTNode)
    (tree : annotatedASTNode nary_tree) =
  let nodes = proof_tree_to_node_list tree in
  let steps = List.tl nodes in
  let rec sublist_before_id lst target_id =
    match lst with
    | [] -> []
    | x :: xs ->
        if x.id = target_id then [] else x :: sublist_before_id xs target_id
  in
  sublist_before_id steps node.id

let last_offset (p : proof) : int =
  List.fold_left
    (fun acc elem ->
      if elem.range.end_.offset > acc then elem.range.end_.offset else acc)
    0
    (p.proposition :: p.proof_steps)

let proof_nodes (p : proof) : annotatedASTNode list =
  p.proposition :: p.proof_steps

let proof_from_nodes (nodes : annotatedASTNode list) : proof =
  { proposition = List.hd nodes; proof_steps = List.tl nodes }

(* take a full tree and return an acc *)
(* fold over the proof while running the expr each time to get a new state *)
let rec depth_first_fold_with_state (doc : Doc.t) (token : Coq.Limits.Token.t)
    (f :
      Petanque.Agent.State.t ->
      'acc ->
      annotatedASTNode ->
      Petanque.Agent.State.t * 'acc) (acc : 'acc)
    (tree : annotatedASTNode nary_tree) : ('acc, string) result =
  let rec aux
      (f :
        Petanque.Agent.State.t -> 'acc -> 'a -> Petanque.Agent.State.t * 'acc)
      (state : Petanque.Agent.State.t) (acc : 'acc) (tree : 'a nary_tree) : 'acc
      =
    match tree with
    | Node (x, children) ->
        let new_acc = f state acc x in
        List.fold_left (aux f (fst new_acc)) (snd new_acc) children
  in
  let proof = tree_to_proof tree in
  match get_init_state doc proof with
  | Some (Ok state) -> Ok (aux f state.st acc tree)
  | _ -> Error "Unable to retrieve initial state"
