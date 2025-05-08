open Fleche
open Vernacexpr

type syntaxNode = {
  ast : Doc.Node.Ast.t option;
  range : Lang.Range.t;
  repr : string;
  id : Uuidm.t;
  proof_id : int option;
  diagnostics : Lang.Diagnostic.t list;
}

val pp_syntax_node : Format.formatter -> syntaxNode -> unit

val syntax_node_of_coq_ast : Coq.Ast.t -> Lang.Point.t -> syntaxNode
(** [syntax_node_of_coq_ast ast starting_point] create a syntax node from a Coq
    AST element and a point to start the node. *)

val comment_syntax_node_of_string :
  string -> Lang.Point.t -> (syntaxNode, string) result
(** [comment_syntax_node_of_string content range] create a syntax node
    representing a comment containing the string content starting at the
    specified point *)

val syntax_node_of_string :
  string -> Lang.Point.t -> (syntaxNode, string) result
(** [syntax_node_of_string code start_point] returns a result [Ok Syntax_node]
    if [code] was parsed as only one syntax node that will be positioned
    starting at [start_point] or [Error string] with a string containing the
    error message detailing why the node was not able to be created *)

val string_of_syntax_node : syntaxNode -> string
val validate_syntax_node : syntaxNode -> (syntaxNode, string) result

val mk_vernac_control :
  ?loc:Loc.t -> synterp_vernac_expr vernac_expr_gen -> vernac_control

val qed_ast_node : Lang.Point.t -> syntaxNode
(** [qed_ast_node] create a syntax node containing the Coq command Qed starting
    at the specified point. *)

val syntax_node_to_yojson : Doc.Node.Ast.t -> Yojson.Safe.t
(** [syntax_node_to_yojson ast_node] converts a syntax node of type
    [Doc.Node.Ast.t] into a [Yojson.Safe.t] representation. *)

val doc_node_of_yojson : Yojson.Safe.t -> Doc.Node.Ast.t
(** [doc_node_of_yojson json] convert a compatible element of type
    [Yojson.Safe.t] into an element of type [Doc.Node.Ast.t] *)

val point_to_yojson : Lang.Point.t -> Yojson.Safe.t
(** [point_to_yojson point] converts a point of type [Lang.Point.t] into a
    [Yojson.Safe.t] representation. *)

val point_of_yojson : Yojson.Safe.t -> Lang.Point.t
(** [point_of_yojson json] convert a compatible element of type [Yojson.Safe.t]
    into an element of type [Lang.Point.t] *)

val range_to_yojson : Lang.Range.t -> Yojson.Safe.t
(** [range_to_yojson range] convert a range of type [Lang.Range.t] into a
    [Yojson.Safe.t] representation. *)

val range_of_yojson : Yojson.Safe.t -> Lang.Range.t
(** [range_of_yojson json] convert a compatible element of type [Yojson.Safe.t]
    into an element of type [Lang.Range.t] *)

val shift_point : int -> int -> int -> Lang.Point.t -> Lang.Point.t
(** [shift_point n_line n_char n_offset point] shift [point] by [n_line],
    [n_char] and [n_offset]. shifting by [n_char] cause the offset to also shift
    by [n_char] in addition to [n_offset] *)

val shift_range : int -> int -> int -> Lang.Range.t -> Lang.Range.t
(** [shift_range n_line n_char n_offset range] shift both points of [range] by
    [n_line], [n_char] and [n_offset]. shifting by [n_char] cause both points
    offset to also shift by [n_char] in addition to [n_offset] *)

val shift_node : int -> int -> int -> syntaxNode -> syntaxNode
(** [shift_node n_line n_char n_offset node] shift the range of [node] by
    [n_line], [n_char] and [n_offset] using [shift_range] *)

val is_syntax_node_ast_proof_command : syntaxNode -> bool
(** [is_syntax_node_ast_proof_command x] checks if [x] represents the command
    Proof. *)

val is_syntax_node_ast_tactic : syntaxNode -> bool
(** [is_syntax_node_ast_tactic x] checks if [x] represents a tactic. *)

val is_syntax_node_bullet : syntaxNode -> bool
(** [is_syntax_node_bullet x] check if [x] is a Coq bullet made of repeated -,
    + or * symbols *)

val is_syntax_node_ast_proof_start : syntaxNode -> bool
(** [is_syntax_node_ast_proof_start x] checks if [x] marks the start of a proof.
    meaning if it's a sentence starting with: Theorem | Lemma | Fact | Remark |
    Property | Proposition | Corollary *)

val is_syntax_node_ast_proof_end : syntaxNode -> bool
(** [is_syntax_node_ast_proof_end x] checks if [x] marks the end of a proof.
    meaning if it's either Qed. or Admitted. *)

val is_syntax_node_ast_proof_command : syntaxNode -> bool
(** [is_syntax_node_ast_proof_command x] check if [x] is the command Proof. *)

val is_syntax_node_proof_intro_or_end : syntaxNode -> bool
(** [is_syntax_node_proof_intro_or_end x] check if [x] is an intro of a proof or
    an end of a proof, meaning if it's either a a sentence starting with:
    Theorem | Lemma | Fact | Remark | Property | Proposition | Corollary or the
    command Proof, Qed or Admitted *)

val is_syntax_node_ast_proof_abort : syntaxNode -> bool
(** [is_syntax_node_ast_proof_abort x] check if [x] abort a proof, meaning it's
    either Abort or Abort all *)

val node_can_open_proof : syntaxNode -> bool
(** [node_can_open_proof x] check if [x] can start a proof, meaning it's either:
    - a sentence starting with: Theorem | Lemma | Fact | Remark | Property |
      Proposition | Corollary
    - a sentence starting with Goal (anonymous goal)
    - an Instance with a proof
    - a Function with a proof *)

val node_can_close_proof : syntaxNode -> bool
(** [node_can_close_proof x] check if [x] can close a proof, meaning it's either
    Qed, Admitted, Abort or Abort all *)

val get_tactic_raw_generic_arguments :
  syntaxNode -> Genarg.raw_generic_argument list option
