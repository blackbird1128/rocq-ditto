open Proof
open Proof_tree
open Syntax_node

val fold_replace_assumption_with_apply :
  Coq_document.t ->
  syntaxNode nary_tree ->
  (transformation_step list, string) result

val id_transform :
  Coq_document.t -> proof -> (transformation_step list, string) result

val remove_unecessary_steps :
  Coq_document.t -> proof -> (transformation_step list, string) result

val fold_add_time_taken :
  Coq_document.t -> proof -> (transformation_step list, string) result

val replace_auto_with_steps :
  Coq_document.t -> proof -> (transformation_step list, string) result

val compress_intro :
  Coq_document.t -> proof -> (transformation_step list, string) result

val cut_replace_branch :
  string ->
  Coq_document.t ->
  syntaxNode nary_tree ->
  (transformation_step list, string) result

val make_intros_explicit :
  Coq_document.t -> proof -> (transformation_step list, string) result

val turn_into_oneliner :
  Coq_document.t ->
  syntaxNode nary_tree ->
  (transformation_step list, string) result

val apply_proof_transformation :
  (Coq_document.t -> Proof.proof -> (transformation_step list, string) result) ->
  Coq_document.t ->
  (Coq_document.t, string) result

val apply_proof_tree_transformation :
  (Coq_document.t ->
  syntaxNode nary_tree ->
  (transformation_step list, string) result) ->
  Coq_document.t ->
  (Coq_document.t, string) result
