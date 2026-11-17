val attach_node_after_pred :
  Rocq_document.t ->
  Syntax_node.t ->
  ?reverse:bool ->
  (Syntax_node.t -> bool) ->
  (Transforming_step.t list, Error.t) result

val attach_node_after_pred_in_file :
  Rocq_document.t ->
  Syntax_node.t ->
  string ->
  ?reverse:bool ->
  (Syntax_node.t -> bool) ->
  (Transforming_step.t list, Error.t) result

val attach_node_after_requires :
  Rocq_document.t -> Syntax_node.t -> (Transforming_step.t list, Error.t) result

val attach_require_to_file :
  Rocq_document.t ->
  require_text:string ->
  string ->
  (Transforming_step.t list, Error.t) result

val get_proofs_named : Proof.t list -> string list -> Proof.t list
