open Fleche

type annotatedASTNode = {
  ast : Doc.Node.Ast.t;
  range : Lang.Range.t;
  repr : string;
  id : int;
  proof_id : int option;
}

val ast_node_of_coq_ast : Coq.Ast.t -> Lang.Range.t -> annotatedASTNode

val ast_node_to_yojson : Doc.Node.Ast.t -> Yojson.Safe.t
(** [ast_node_to_yojson ast_node] converts an AST node of type [Doc.Node.Ast.t] 
    into a Yojson.Safe.t representation. *)

val ast_node_of_yojson : Yojson.Safe.t -> Doc.Node.Ast.t

val point_to_yojson : Lang.Point.t -> Yojson.Safe.t
(** [point_to_yojson point] converts a point of type [Lang.Point.t] 
    into a Yojson.Safe.t representation. *)

val point_of_yojson : Yojson.Safe.t -> Lang.Point.t

val range_to_yojson : Lang.Range.t -> Yojson.Safe.t
(** [range_to_yojson range] converts a range of type [Lang.Range.t] 
    into a Yojson.Safe.t representation. *)

val range_of_yojson : Yojson.Safe.t -> Lang.Range.t

val to_yojson : annotatedASTNode -> Yojson.Safe.t
(** [to_yojson node] converts an annotated AST node of type [annotatedASTNode] 
    into a Yojson.Safe.t representation. *)

val of_yojson : Yojson.Safe.t -> annotatedASTNode
val shift_point : int -> int -> Lang.Point.t -> Lang.Point.t
val shift_node : int -> int -> annotatedASTNode -> annotatedASTNode

val is_doc_node_ast_tactic : annotatedASTNode -> bool
(** [is_doc_node_ast_tactic x] checks if [x] represents a tactic in the Coq document. *)

val is_doc_node_ast_proof_start : annotatedASTNode -> bool
(** [is_doc_node_ast_proof_start x] checks if [x] marks the start of a proof in the Coq document. *)

val is_doc_node_ast_proof_end : annotatedASTNode -> bool
(** [is_doc_node_ast_proof_end x] checks if [x] marks the end of a proof in the Coq document. *)

val is_doc_node_ast_proof_command : annotatedASTNode -> bool
