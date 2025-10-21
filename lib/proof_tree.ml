open Nary_tree
open Syntax_node
open Proof

type proof_tree = Syntax_node.t nary_tree

let apply_transformation_step (step : transformation_step)
    (proof_tree : proof_tree) : (proof_tree, Error.t) result =
  match step with
  | Remove node_to_remove_id ->
      Option.cata
        (fun x -> Ok x)
        (Error.string_to_or_error_err
           "Removed the last node of the tree or the tree root")
        (filter (fun node -> node.id != node_to_remove_id) proof_tree)
  | Replace (node_to_replace_id, new_node) ->
      Ok
        (map
           (fun node -> if node.id = node_to_replace_id then new_node else node)
           proof_tree)
  | Add _ ->
      Error.string_to_or_error_err
        "WIP: adding a new node throught a transformation step not supported \
         yet"
  | Attach _ ->
      Error.string_to_or_error_err
        "WIP: applying attach transformation step not supported yet"

let apply_transformations_steps (steps : transformation_step list)
    (proof_tree : proof_tree) : (proof_tree, Error.t) result =
  List.fold_left
    (fun proof_tree_acc step ->
      match proof_tree_acc with
      | Ok acc -> apply_transformation_step step acc
      | Error err -> Error err)
    (Ok proof_tree) steps
