open Nary_tree
open Syntax_node
open Transforming_step

type proof_tree = Syntax_node.t Nary_tree.t

let apply_transformation_step (step : Transforming_step.t)
    (proof_tree : proof_tree) : (proof_tree, Error.t) result =
  match step with
  | Remove node_to_remove_id ->
      Option.cata
        (fun x -> Ok x)
        (Error.string_to_or_error
           "Removed the last node of the tree or the tree root")
        (filter (fun node -> node.id != node_to_remove_id) proof_tree)
  | Replace (node_to_replace_id, new_node) ->
      Ok
        (map
           (fun node -> if node.id = node_to_replace_id then new_node else node)
           proof_tree)
  | Add _ ->
      Error.string_to_or_error
        "WIP: adding a new node throught a transformation step not supported \
         yet"
  | Attach _ ->
      Error.string_to_or_error
        "WIP: applying attach transformation step not supported yet"

type parent_category = Fork | Linear

let rec pop_until_free_fork
    (prev_pars : (int * int * Syntax_node.t * parent_category) list)
    (parents : (int * Syntax_node.t, int * Syntax_node.t) Hashtbl.t) :
    (int * int * Syntax_node.t * parent_category) list =
  match prev_pars with
  | [] -> []
  | (goal_count, par_id, par_node, cat_par) :: tail_par -> (
      match cat_par with
      | Fork ->
          let childs_count =
            List.length (Hashtbl.find_all parents (par_id, par_node))
          in
          if childs_count < goal_count then prev_pars
          else pop_until_free_fork tail_par parents
      | Linear -> pop_until_free_fork tail_par parents)

let rec get_parents_rec (steps_with_goals : (int * Syntax_node.t * int) list)
    (prev_pars : (int * int * Syntax_node.t * parent_category) list) (idx : int)
    (parents : (int * Syntax_node.t, int * Syntax_node.t) Hashtbl.t) =
  match steps_with_goals with
  | [] -> parents
  | (prev_goals, step, new_goals) :: tail -> (
      match prev_pars with
      | [] ->
          if new_goals > prev_goals then
            get_parents_rec tail
              [ (new_goals - prev_goals + 1, idx, step, Fork) ]
              (idx + 1) parents
          else
            get_parents_rec tail
              [ (new_goals, idx, step, Linear) ]
              (idx + 1) parents
      | (_, idx_par, tactic_par, _) :: _ ->
          let par = (idx_par, tactic_par) in
          if new_goals < prev_goals then (
            Hashtbl.add parents par (idx, step);
            if new_goals > 0 then
              get_parents_rec tail
                (pop_until_free_fork prev_pars parents)
                (idx + 1) parents
            else
              get_parents_rec tail
                [ (new_goals, idx, step, Linear) ]
                (idx + 1) parents)
          else if new_goals = prev_goals then (
            Hashtbl.add parents par (idx, step);
            get_parents_rec tail
              ((new_goals, idx, step, Linear) :: prev_pars)
              (idx + 1) parents)
          else (
            Hashtbl.add parents par (idx, step);
            get_parents_rec tail
              ((new_goals - prev_goals + 1, idx, step, Fork) :: prev_pars)
              (idx + 1) parents))

let rec proof_tree_from_parents (cur_node : int * Syntax_node.t)
    (parents : (int * Syntax_node.t, int * Syntax_node.t) Hashtbl.t) :
    Syntax_node.t Nary_tree.t =
  let _, tactic = cur_node in
  let childs = Hashtbl.find_all parents cur_node in
  Node
    ( tactic,
      List.rev_map (fun node -> proof_tree_from_parents node parents) childs )

let treeify_proof (doc : Rocq_document.t) (p : Proof.t) :
    (Syntax_node.t Nary_tree.t, Error.t) result =
  let ( let* ) = Result.bind in
  let token = Coq.Limits.Token.create () in
  match Runner.get_init_state doc p.opening token with
  | Ok init_state ->
      let* steps_with_goals =
        Runner.proof_steps_with_goalcount token init_state (Proof.all_nodes p)
      in

      let parents = Hashtbl.create (List.length steps_with_goals) in
      let _ = get_parents_rec steps_with_goals [] 0 parents in
      Ok (proof_tree_from_parents (0, p.opening) parents)
  | Error err -> Error err

let rec proof_tree_to_node_list (Node (value, children)) : Syntax_node.t list =
  value :: List.concat (List.map proof_tree_to_node_list children)

let tree_to_proof (tree : Syntax_node.t Nary_tree.t) : (Proof.t, Error.t) result
    =
  let nodes = proof_tree_to_node_list tree in
  Proof.of_nodes nodes
