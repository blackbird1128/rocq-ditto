open Fleche
open Petanque
open Syntax_node
open Vernacexpr
open Proof_tree

type proof_status = Admitted | Proved | Aborted

let pp_proof_status (fmt : Format.formatter) (status : proof_status) : unit =
  match status with
  | Admitted -> Format.fprintf fmt "Admitted"
  | Proved -> Format.fprintf fmt "Proved"
  | Aborted -> Format.fprintf fmt "Aborted"

type transformation_step =
  | Remove of int
  | Replace of int * syntaxNode
  | Add of syntaxNode

let pp_transformation_step (fmt : Format.formatter) (step : transformation_step)
    : unit =
  match step with
  | Remove id -> Format.fprintf fmt "Removing node with id : %d." id
  | Replace (id, new_node) ->
      if new_node.range.start.line != new_node.range.end_.line then
        Format.fprintf fmt "Replacing node with id: %d by node: %s at %s" id
          new_node.repr
          (Lang.Range.to_string new_node.range)
  | Add new_node ->
      Format.fprintf fmt "Adding new node: %s at %s" new_node.repr
        (Lang.Range.to_string new_node.range)

type proof = {
  proposition : syntaxNode;
  proof_steps : syntaxNode list;
  status : proof_status;
}
(* proposition can also be a type, better name ? *)

(* A node can have multiple names (ie mutual recursive defs) *)
let get_names (node : syntaxNode) : string list =
  match node.ast with
  | Some ast -> (
      match ast.ast_info with
      | Some infos ->
          List.concat_map
            (fun (info : Lang.Ast.Info.t) ->
              match info.name.v with None -> [] | Some s -> [ s ])
            infos
      | None -> [])
  | None -> []

let proof_status_from_last_node (node : syntaxNode) :
    (proof_status, string) result =
  match node.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).CAst.v.expr with
      | VernacSynterp _ -> Error "not a valid closing node"
      | VernacSynPure expr -> (
          match expr with
          | Vernacexpr.VernacEndProof proof_end -> (
              match proof_end with
              | Admitted -> Ok Admitted
              | Proved _ -> Ok Proved)
          | Vernacexpr.VernacAbort -> Ok Aborted
          | Vernacexpr.VernacAbortAll -> Ok Aborted
          | _ -> Error "not a valid closing node"))
  | None -> Error "not a valid closing node (no ast)"

let get_proof_name (p : proof) : string option =
  List.nth_opt (get_names p.proposition) 0

let get_tree_name (Node (x, children)) : string option =
  List.nth_opt (get_names x) 0

let doc_node_to_string (d : Doc.Node.Ast.t) : string =
  let pp_expr = Ppvernac.pr_vernac_expr (Coq.Ast.to_coq d.v).CAst.v.expr in
  Pp.string_of_ppcmds pp_expr

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

let print_proof (proof : proof) : unit =
  print_endline proof.proposition.repr;
  List.iter (fun p -> print_endline ("  " ^ p.repr)) proof.proof_steps

let rec print_tree (tree : syntaxNode nary_tree) (indent : string) : unit =
  match tree with
  | Node (value, children) ->
      Printf.printf "%sNode(%s)\n" indent value.repr;
      List.iter (fun child -> print_tree child (indent ^ "  ")) children

let rec proof_steps_with_goalcount (token : Coq.Limits.Token.t)
    (st : Agent.State.t) (steps : syntaxNode list) : (syntaxNode * int) list =
  match steps with
  | [] -> []
  | step :: tail ->
      let state = Agent.run ~token ~st ~tac:step.repr () in
      let agent_state = get_proof_state state in
      let goal_count = count_goals token agent_state in
      (step, goal_count) :: proof_steps_with_goalcount token agent_state tail

let print_parents (parents : (int * syntaxNode, int * syntaxNode) Hashtbl.t) :
    unit =
  Hashtbl.iter
    (fun (k_idx, k_tactic) (v_idx, v_tactic) ->
      Printf.printf
        "Parent: (idx: %d, tactic: %s) -> Child: (idx: %d, tactic: %s)\n" k_idx
        k_tactic.repr v_idx v_tactic.repr)
    parents

type parent_category = Fork | Linear

let rec pop_until_fork (prev_pars : (int * syntaxNode * parent_category) list) :
    (int * syntaxNode * parent_category) list =
  match prev_pars with
  | [] -> []
  | (_, _, cat_par) :: tail_par -> (
      match cat_par with Fork -> prev_pars | Linear -> pop_until_fork tail_par)

let rec get_parents_rec (steps_with_goals : (syntaxNode * int) list)
    (prev_goals : int) (prev_pars : (int * syntaxNode * parent_category) list)
    (idx : int) (parents : (int * syntaxNode, int * syntaxNode) Hashtbl.t) =
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

let rec proof_tree_from_parents (cur_node : int * syntaxNode)
    (parents : (int * syntaxNode, int * syntaxNode) Hashtbl.t) :
    syntaxNode nary_tree =
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

let treeify_proof (doc : Doc.t) (p : proof) :
    (syntaxNode nary_tree, string) result =
  let token = Coq.Limits.Token.create () in

  match get_init_state doc p with
  | Some init_state ->
      let init_state = Option.get (get_init_state doc p) in
      let proof_state = get_proof_state init_state in
      let steps_with_goals =
        proof_steps_with_goalcount token proof_state p.proof_steps
      in

      let parents = Hashtbl.create (List.length steps_with_goals) in

      let _ = get_parents_rec steps_with_goals 1 [] 0 parents in
      Ok
        (Node
           ( p.proposition,
             [ proof_tree_from_parents (0, List.hd p.proof_steps) parents ] ))
  | None -> Error "Unable to retrieve initial state"

let rec proof_tree_to_node_list (Node (value, children)) : syntaxNode list =
  value :: List.concat (List.map proof_tree_to_node_list children)

let tree_to_proof (tree : syntaxNode nary_tree) : proof =
  let nodes = proof_tree_to_node_list tree in
  let last_node_status =
    List.hd (List.rev nodes) |> proof_status_from_last_node
  in
  {
    proposition = List.hd nodes;
    proof_steps = List.tl nodes;
    status = Result.get_ok last_node_status;
  }

let previous_steps_from_tree (node : syntaxNode) (tree : syntaxNode nary_tree) =
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

let proof_nodes (p : proof) : syntaxNode list = p.proposition :: p.proof_steps

let proof_from_nodes (nodes : syntaxNode list) : (proof, string) result =
  if List.length nodes < 3 then
    Error "Not enough elements to create a proof from the nodes ."
  else
    let last_node_status =
      List.hd (List.rev nodes) |> proof_status_from_last_node
    in
    match last_node_status with
    | Ok status ->
        Ok { proposition = List.hd nodes; proof_steps = List.tl nodes; status }
    | Error err -> Error err

let get_current_goal (token : Coq.Limits.Token.t) (state : Agent.State.t) :
    (string Coq.Goals.Reified_goal.t, string) result =
  let goals_err_opt = Petanque.Agent.goals ~token ~st:state in
  match goals_err_opt with
  | Ok (Some goals) -> (
      match List.nth_opt goals.goals 0 with
      | Some goal -> Ok goal
      | None -> Error "zero goal at this state")
  | Ok None -> Error "zero goal at this state"
  | Error err -> Error (Agent.Error.to_string err)

let get_hypothesis_names (goal : string Coq.Goals.Reified_goal.t) : string list
    =
  List.concat_map
    (fun (hyp : string Coq.Goals.Reified_goal.hyp) -> hyp.names)
    goal.hyps

(* take a full tree and return an acc *)
(* fold over the proof while running the expr each time to get a new state *)
let rec depth_first_fold_with_state (doc : Doc.t) (token : Coq.Limits.Token.t)
    (f :
      Petanque.Agent.State.t ->
      'acc ->
      syntaxNode ->
      Petanque.Agent.State.t * 'acc) (acc : 'acc) (tree : syntaxNode nary_tree)
    : ('acc, string) result =
  let rec aux
      (f :
        Petanque.Agent.State.t -> 'acc -> 'a -> Petanque.Agent.State.t * 'acc)
      (state : Petanque.Agent.State.t) (acc : 'acc) (tree : 'a nary_tree) :
      Petanque.Agent.State.t * 'acc =
    match tree with
    | Node (x, children) ->
        let state, acc = f state acc x in
        (* Fold over the children using the updated state and accumulator *)
        List.fold_left
          (fun (state, acc) child ->
            let new_state, new_acc = aux f state acc child in
            (new_state, new_acc))
          (state, acc) children
    (* Fold over the children, threading the state and updating acc *)
    (* Update state and accumulator for the current node *)
  in

  let proof = tree_to_proof tree in
  match get_init_state doc proof with
  | Some (Ok state) -> Ok (snd (aux f state.st acc tree))
  | _ -> Error "Unable to retrieve initial state"

let rec fold_nodes_with_state (doc : Doc.t) (token : Coq.Limits.Token.t)
    (f :
      Petanque.Agent.State.t ->
      'acc ->
      syntaxNode ->
      Petanque.Agent.State.t * 'acc) (init_state : Petanque.Agent.State.t)
    (acc : 'acc) (l : syntaxNode list) : 'acc =
  let rec aux (l : syntaxNode list) (state : Petanque.Agent.State.t)
      (acc : 'acc) =
    match l with
    | [] -> acc
    | x :: tail ->
        let res = f state acc x in
        aux tail (fst res) (snd res)
  in
  aux l init_state acc

let rec fold_proof_with_state (doc : Doc.t) (token : Coq.Limits.Token.t)
    (f :
      Petanque.Agent.State.t ->
      'acc ->
      syntaxNode ->
      Petanque.Agent.State.t * 'acc) (acc : 'acc) (p : proof) :
    ('acc, string) result =
  let proof_nodes = proof_nodes p in
  let rec aux (l : syntaxNode list) (state : Petanque.Agent.State.t)
      (acc : 'acc) =
    match l with
    | [] -> acc
    | x :: tail ->
        let res = f state acc x in
        aux tail (fst res) (snd res)
  in
  match get_init_state doc p with
  | Some (Ok state) -> Ok (aux proof_nodes state.st acc)
  | _ -> Error "Unable to retrieve initial state"
