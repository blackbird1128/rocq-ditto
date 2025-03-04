open Fleche

type syntaxNode = {
  ast : Doc.Node.Ast.t option;
  range : Lang.Range.t;
  repr : string;
  id : int;
  proof_id : int option;
}

val pp_syntax_node : Format.formatter -> syntaxNode -> unit
val syntax_node_of_coq_ast : Coq.Ast.t -> Lang.Range.t -> syntaxNode

val comment_syntax_node_of_string :
  string -> Lang.Range.t -> (syntaxNode, string) result

val syntax_node_of_string :
  string -> Lang.Range.t -> (syntaxNode, string) result

val qed_ast_node : Lang.Range.t -> syntaxNode

val syntax_node_to_yojson : Doc.Node.Ast.t -> Yojson.Safe.t
(** [syntax_node_to_yojson ast_node] converts a syntax node of type
    [Doc.Node.Ast.t] into a Yojson.Safe.t representation. *)

val syntax_node_of_yojson : Yojson.Safe.t -> Doc.Node.Ast.t

val point_to_yojson : Lang.Point.t -> Yojson.Safe.t
(** [point_to_yojson point] converts a point of type [Lang.Point.t] into a
    Yojson.Safe.t representation. *)

val point_of_yojson : Yojson.Safe.t -> Lang.Point.t

val range_to_yojson : Lang.Range.t -> Yojson.Safe.t
(** [range_to_yojson range] converts a range of type [Lang.Range.t] into a
    Yojson.Safe.t representation. *)

val range_of_yojson : Yojson.Safe.t -> Lang.Range.t

val to_yojson : syntaxNode -> Yojson.Safe.t
(** [to_yojson node] converts a syntax node of type [syntaxNode] into a
    Yojson.Safe.t representation. *)

val of_yojson : Yojson.Safe.t -> syntaxNode
val shift_point : int -> int -> int -> Lang.Point.t -> Lang.Point.t
val shift_range : int -> int -> int -> Lang.Range.t -> Lang.Range.t
val shift_node : int -> int -> int -> syntaxNode -> syntaxNode

val is_doc_node_ast_proof_command : syntaxNode -> bool
(** [is_doc_node_ast_proof_command x] checks if [x] represents the command
    Proof. *)

val is_doc_node_ast_tactic : syntaxNode -> bool
(** [is_doc_node_ast_tactic x] checks if [x] represents a tactic. *)

val is_doc_node_ast_proof_start : syntaxNode -> bool
(** [is_doc_node_ast_proof_start x] checks if [x] marks the start of a proof. *)

val is_doc_node_ast_proof_end : syntaxNode -> bool
(** [is_doc_node_ast_proof_end x] checks if [x] marks the end of a proof in the
    Coq document. *)

val is_doc_node_ast_proof_command : syntaxNode -> bool
val is_doc_node_proof_intro_or_end : syntaxNode -> bool
val is_doc_node_ast_proof_abort : syntaxNode -> bool
val node_can_open_proof : syntaxNode -> bool
val node_can_close_proof : syntaxNode -> bool
