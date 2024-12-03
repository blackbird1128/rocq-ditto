open Fleche
open Petanque

type proof = { proposition : Doc.Node.Ast.t; proof_steps : Doc.Node.Ast.t list }
(* proposition can also be a type, better name ? *)

(* A node can have multiple names (ie mutual recursive defs) *)
let get_names (infos : Lang.Ast.Info.t list) =
  List.concat_map
    (fun (info : Lang.Ast.Info.t) ->
      match info.name.v with None -> [] | Some s -> [ s ])
    infos

let get_proof_name (p : proof) : string option =
  if Option.has_some p.proposition.ast_info then
    (Option.get p.proposition.ast_info |> get_names |> List.nth_opt) 0
  else None

let doc_node_to_string (d : Doc.Node.Ast.t) : string =
  Ppvernac.pr_vernac (Coq.Ast.to_coq d.v) |> Pp.string_of_ppcmds

let proof_to_coq_script_string (p : proof) : string =
  doc_node_to_string p.proposition
  ^ "\n"
  ^ String.concat "\n" (List.map (fun n -> doc_node_to_string n) p.proof_steps)

let is_doc_node_ast_tactic (x : Doc.Node.Ast.t) : bool =
  match (Coq.Ast.to_coq x.v).CAst.v.expr with
  | VernacSynterp synterp_expr -> (
      match synterp_expr with VernacExtend (_, _) -> false | _ -> false)
  | VernacSynPure _ -> false

let is_doc_node_ast_tactic (x : Doc.Node.Ast.t) : bool =
  match (Coq.Ast.to_coq x.v).CAst.v.expr with
  | VernacSynterp synterp_expr -> (
      match synterp_expr with
      | VernacExtend (ext, _) ->
          if ext.ext_plugin = "coq-core.plugins.ltac" then true else false
      | _ -> false)
  | VernacSynPure _ -> false

let is_doc_node_ast_proof_start (x : Doc.Node.Ast.t) : bool =
  match (Coq.Ast.to_coq x.v).CAst.v.expr with
  | VernacSynterp _ -> false
  | VernacSynPure expr -> (
      match expr with
      | Vernacexpr.VernacStartTheoremProof _ -> true
      | _ -> false)

let is_doc_node_ast_proof_end (x : Doc.Node.Ast.t) : bool =
  match (Coq.Ast.to_coq x.v).CAst.v.expr with
  | VernacSynterp _ -> false
  | VernacSynPure expr -> (
      match expr with Vernacexpr.VernacEndProof _ -> true | _ -> false)

let get_tactics (p : proof) : string list =
  List.filter is_doc_node_ast_tactic p.proof_steps
  |> List.map doc_node_to_string

type 'a nary_tree = Node of 'a * 'a nary_tree list

let get_proof_state start_result =
  match start_result with
  | Ok run_result -> run_result
  | Error err ->
      Printf.eprintf "Error: %s\n" (Agent.Error.to_string err);
      raise (Failure "Failed to start proof")

(** count the number of goalf of a state *)
let count_goals (token : Coq.Limits.Token.t) (st : Agent.State.t) : int =
  let goals = Agent.goals ~token ~st in
  match goals with
  | Ok (Some reified_goals) -> List.length reified_goals.goals
  | Ok None -> 0
  | Error _ -> 0

let rec print_tree tree indent =
  match tree with
  | Node (value, children) ->
      Printf.printf "%sNode(%s)\n" indent value;
      List.iter (fun child -> print_tree child (indent ^ "  ")) children

let rec tactics_with_goalcount (token : Coq.Limits.Token.t) (st : Agent.State.t)
    (tactics : string list) : (string * int) list =
  match tactics with
  | [] -> []
  | tactic :: tail ->
      let state = Agent.run ~token ~st ~tac:tactic () in
      let agent_state = (get_proof_state state).st in
      let goal_count = count_goals token agent_state in
      (tactic, goal_count) :: tactics_with_goalcount token agent_state tail

let rec treeify_proof_rec (tactics_with_goals : (string * int) list)
    (old_goals : int) : string nary_tree * (string * int) list =
  match tactics_with_goals with
  | [] -> (Node ("empty", []), [])
  | (tactic, new_goals) :: tail ->
      if new_goals < old_goals then (Node (tactic, []), tail)
      else if new_goals = old_goals then
        let subtree, tail_f = treeify_proof_rec tail new_goals in
        (Node (tactic, [ subtree ]), tail_f)
      else
        let dummy = List.init new_goals (fun _ -> ()) in
        let remaining, subtrees =
          List.fold_left
            (fun (remaining_tactics, subtrees) _ ->
              let goals_opt =
                Option.map snd (List.nth_opt remaining_tactics 0)
              in
              let goals = Option.default new_goals goals_opt in
              let subtree, tail_f = treeify_proof_rec remaining_tactics goals in

              (tail_f, subtree :: subtrees))
            (tail, []) dummy
        in
        (Node (tactic, List.rev subtrees), remaining)

let treeify_proof (p : proof) (doc : Doc.t) : string nary_tree =
  let token = Coq.Limits.Token.create () in
  let proof_name_opt = get_proof_name p in
  let proof_name = Option.get proof_name_opt in
  let tactics = get_tactics p in
  let init_state = Agent.start ~token ~doc ~thm:proof_name () in
  let proof_state = (get_proof_state init_state).st in
  let tactics_with_goals = tactics_with_goalcount token proof_state tactics in
  List.iter
    (fun (tactic, goal_count) ->
      print_endline (tactic ^ " " ^ string_of_int goal_count))
    tactics_with_goals;
  fst (treeify_proof_rec tactics_with_goals 1)
