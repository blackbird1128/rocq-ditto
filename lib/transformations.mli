open Proof
open Proof_tree
open Syntax_node

val error_location_to_string : Lang.Range.t -> string

val fold_replace_assumption_with_apply :
  Coq_document.t ->
  syntaxNode nary_tree ->
  (transformation_step list, string) result

val remove_unecessary_steps :
  Coq_document.t -> proof -> (transformation_step list, string) result

val fold_add_time_taken :
  Coq_document.t -> proof -> (transformation_step list, string) result

val replace_auto_with_info_auto :
  Coq_document.t -> proof -> (transformation_step list, string) result

val make_intros_explicit :
  Coq_document.t -> proof -> (transformation_step list, string) result

val apply_proof_transformation :
  (Coq_document.t -> Proof.proof -> (transformation_step list, string) result) ->
  Coq_document.t ->
  Proof.proof ->
  (Coq_document.t, string) result
