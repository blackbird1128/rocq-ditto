open Proof
open Nary_tree

val map_raw_tactic_expr_in_node :
  (Ltac_plugin.Tacexpr.raw_tactic_expr -> Ltac_plugin.Tacexpr.raw_tactic_expr) ->
  Syntax_node.t ->
  Proof.transformation_step option

val fold_replace_assumption_with_apply :
  Rocq_document.t ->
  Syntax_node.t nary_tree ->
  (transformation_step list, Error.t) result

val id_transform :
  Rocq_document.t -> Proof.t -> (transformation_step list, Error.t) result

val remove_unecessary_steps :
  Rocq_document.t -> Proof.t -> (transformation_step list, Error.t) result

val fold_add_time_taken :
  Rocq_document.t -> Proof.t -> (transformation_step list, Error.t) result

val replace_auto_with_steps :
  Rocq_document.t -> Proof.t -> (transformation_step list, Error.t) result

val compress_intro :
  Rocq_document.t -> Proof.t -> (transformation_step list, Error.t) result

val admit_proof :
  Rocq_document.t -> Proof.t -> (transformation_step list, Error.t) result

val admit_and_comment_proof_steps :
  ?msg:string ->
  Rocq_document.t ->
  Proof.t ->
  (transformation_step list, Error.t) result

val remove_random_step :
  Rocq_document.t -> Proof.t -> (transformation_step list, Error.t) result

val simple_proof_repair :
  Rocq_document.t ->
  Syntax_node.t nary_tree ->
  (transformation_step list, Error.t) result

val explicit_fresh_variables :
  Rocq_document.t -> Proof.t -> (transformation_step list, Error.t) result

val rename_definition :
  Rocq_document.t -> (transformation_step list, Error.t) result

val remove_proof_with :
  Rocq_document.t -> Proof.t -> (transformation_step list, Error.t) result

val flatten_goal_selectors :
  Rocq_document.t -> Proof.t -> (transformation_step list, Error.t) result

val turn_into_oneliner :
  Rocq_document.t ->
  Syntax_node.t nary_tree ->
  (transformation_step list, Error.t) result

val rewrite_node_tacexpr :
  Coq.Limits.Token.t ->
  Coq.State.t ->
  f:
    (Coq.State.t ->
    Coq.State.t ->
    Ltac_plugin.Tacexpr.raw_tactic_expr ->
    Ltac_plugin.Tacexpr.raw_tactic_expr) ->
  Syntax_node.t ->
  (Syntax_node.t, Error.t) result

val rewrite_proof_nodes :
  Rocq_document.t ->
  Proof.t ->
  rewrite:
    (Coq.Limits.Token.t ->
    Coq.State.t ->
    Syntax_node.t ->
    (Syntax_node.t, Error.t) result) ->
  (transformation_step list, Error.t) result

val replace_induction_by_destruct_when_possible :
  Rocq_document.t -> Proof.t -> (transformation_step list, Error.t) result

val name_identifier_in_intro :
  Rocq_document.t -> Proof.t -> (transformation_step list, Error.t) result

val explicit_apply :
  Rocq_document.t -> Proof.t -> (transformation_step list, Error.t) result

val add_proof_node_if_missing :
  Rocq_document.t -> Proof.t -> (transformation_step list, Error.t) result

val apply_proof_transformation :
  (Rocq_document.t -> Proof.t -> (transformation_step list, Error.t) result) ->
  Rocq_document.t ->
  (Rocq_document.t, Error.t) result

val apply_proof_tree_transformation :
  (Rocq_document.t ->
  Syntax_node.t nary_tree ->
  (transformation_step list, Error.t) result) ->
  Rocq_document.t ->
  (Rocq_document.t, Error.t) result
