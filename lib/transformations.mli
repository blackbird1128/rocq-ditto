open Proof
open Proof_tree
open Syntax_node

val fold_replace_assumption_with_apply :
  Coq_document.t ->
  syntaxNode nary_tree ->
  (transformation_step list, Error.t) result

val id_transform :
  Coq_document.t -> proof -> (transformation_step list, Error.t) result

val remove_unecessary_steps :
  Coq_document.t -> proof -> (transformation_step list, Error.t) result

val fold_add_time_taken :
  Coq_document.t -> proof -> (transformation_step list, Error.t) result

val replace_auto_with_steps :
  Coq_document.t -> proof -> (transformation_step list, Error.t) result

val compress_intro :
  Coq_document.t -> proof -> (transformation_step list, Error.t) result

val admit_proof :
  Coq_document.t -> proof -> (transformation_step list, Error.t) result

val admit_and_comment_proof_steps :
  Coq_document.t -> proof -> (transformation_step list, Error.t) result

val remove_random_step :
  Coq_document.t -> proof -> (transformation_step list, Error.t) result

val admit_branch_at_error :
  Coq_document.t ->
  syntaxNode nary_tree ->
  (transformation_step list, Error.t) result

val cut_replace_branch :
  string ->
  Coq_document.t ->
  syntaxNode nary_tree ->
  (transformation_step list, Error.t) result

val make_intros_explicit :
  Coq_document.t -> proof -> (transformation_step list, Error.t) result

val turn_into_oneliner :
  Coq_document.t ->
  syntaxNode nary_tree ->
  (transformation_step list, Error.t) result

val apply_proof_transformation :
  (Coq_document.t -> Proof.proof -> (transformation_step list, Error.t) result) ->
  Coq_document.t ->
  (Coq_document.t, Error.t) result

val apply_proof_tree_transformation :
  (Coq_document.t ->
  syntaxNode nary_tree ->
  (transformation_step list, Error.t) result) ->
  Coq_document.t ->
  (Coq_document.t, Error.t) result
