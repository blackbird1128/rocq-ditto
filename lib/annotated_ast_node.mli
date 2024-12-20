open Fleche

type annotatedASTNode = {
  ast : Doc.Node.Ast.t;
  range : Lang.Range.t;
  repr : string;
  id : int;
  proof_id : int option;
}

val shift_point : int -> int -> Lang.Point.t -> Lang.Point.t
val shift_node : int -> int -> annotatedASTNode -> annotatedASTNode

val is_doc_node_ast_tactic : annotatedASTNode -> bool
(** [is_doc_node_ast_tactic x] checks if [x] represents a tactic in the Coq document. *)

val is_doc_node_ast_proof_start : annotatedASTNode -> bool
(** [is_doc_node_ast_proof_start x] checks if [x] marks the start of a proof in the Coq document. *)

val is_doc_node_ast_proof_end : annotatedASTNode -> bool
(** [is_doc_node_ast_proof_end x] checks if [x] marks the end of a proof in the Coq document. *)

val is_doc_node_ast_proof_command : annotatedASTNode -> bool
