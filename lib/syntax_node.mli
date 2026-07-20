open Fleche
open Vernacexpr

type t = {
  ast : Doc.Node.Ast.t option;
  range : Code_range.t;
  repr : string Lazy.t;
  id : Uuidm.t;
  diagnostics : Lang.Diagnostic.t list;
}

val repr : t -> string
val compare : t -> t -> int
val are_colliding : t -> t -> bool
val vernac_expr : t -> synterp_vernac_expr vernac_expr_gen option
val synpure_expr : t -> synpure_vernac_expr option
val synterp_expr : t -> synterp_vernac_expr option

val colliding_nodes : t -> t list -> t list
(** [colliding_nodes target nodes_list] return the nodes in [nodes_lists]
    colliding with [target] *)

val of_doc_node : string -> Doc.Node.t -> t

val of_coq_ast : Coq.Ast.t -> Code_point.t -> t
(** [of_coq_ast ast starting_point] create a syntax node from a Coq AST element
    and a point to start the node. *)

val of_coq_ast_in_state :
  token:Coq.Limits.Token.t ->
  st:Coq.State.t ->
  Coq.Ast.t ->
  Code_point.t ->
  (t, Error.t) result

val of_vernacexpr : Vernacexpr.vernac_expr -> Code_point.t -> t

val of_vernacexpr_in_state :
  token:Coq.Limits.Token.t ->
  st:Coq.State.t ->
  Vernacexpr.vernac_expr ->
  Code_point.t ->
  (t, Error.t) result

val comment_of_string : string -> Code_point.t -> (t, Error.t) result
(** [comment_of_string content range] create a syntax node representing a
    comment containing the string content starting at the specified point *)

val syntax_node_of_string : string -> Code_point.t -> (t, Error.t) result
(** [syntax_node_of_string code start_point] returns a result [Ok Syntax_node]
    if [code] was parsed as only one syntax node that will be positioned
    starting at [start_point] or [Error string] with a string containing the
    error message detailing why the node was not able to be created *)

val reformat : t -> (t, Error.t) result
(** [reformat node] reformat a node. The [node] is reformatted by turning it
    into a coq_ast and then using pr_vernac to reformat the string. Return
    [Error] if [node.ast] is none. *)

val validate : t -> (t, Error.t) result

val mk_vernac_control :
  ?loc:Loc.t -> synterp_vernac_expr vernac_expr_gen -> vernac_control

val shift_node : int -> int -> t -> t
(** [shift_node n_line n_char node] shift the range of [node] by [n_line],
    [n_char] using [shift_range] *)

val move_to : Code_point.t -> t -> t
(** [move_to destination node] Shift node to [destination] point *)

val is_command_allowed_in_proof : t -> bool
(** [is_command_allowed_in_proof x] checks if [x] is a command allowed inside a
    proof block context *)

val is_proof_with : t -> bool
val get_proof_with_tactic : t -> string option
val is_ending_with_ellipsis : t -> bool

val is_ltac : t -> bool
(** [is_ltac x] checks if [x] represents a tactic. *)

val is_bullet : t -> bool
(** [is_bullet x] check if [x] is a Rocq bullet made of repeated -,
    + or * symbols *)

val is_opening_bracket : t -> bool
val is_closing_bracket : t -> bool
val is_focusing_goal : t -> bool

val is_focus_command : t -> bool
(** [is_focus_command] check if [x] is the command [Focus] *)

val is_definition : t -> bool
(** [is_definition] check if [x] is the command [Definition] *)

val is_goal : t -> bool
(** [is_goal] check if [x] is the command [Goal] *)

val get_definition_name : t -> string option
val get_definition_constrexpr : t -> Constrexpr.constr_expr option

val is_proof_start : t -> bool
(** [is_proof_start x] checks if [x] marks the start of a proof. meaning if it's
    a sentence starting with: Theorem | Lemma | Fact | Remark | Property |
    Proposition | Corollary *)

val is_proof_end : t -> bool
(** [is_proof_end x] checks if [x] marks the end of a proof. meaning if it's
    either Qed. or Admitted. *)

val is_proof_command : t -> bool
(** [is_proof_command x] check if [x] is the command Proof. *)

val is_context : t -> bool
(** [is_context x] check if [x] is a context command. *)

val is_require : t -> bool
(** [is_require x] check if [x] is the Require command. *)

val is_proof_intro_or_end : t -> bool
(** [is_proof_intro_or_end x] check if [x] is an intro of a proof or an end of a
    proof, meaning if it's either a a sentence starting with: Theorem | Lemma |
    Fact | Remark | Property | Proposition | Corollary or the command Proof, Qed
    or Admitted *)

val is_proof_abort : t -> bool
(** [is_proof_abort x] check if [x] abort a proof, meaning it's either Abort or
    Abort all *)

val can_open_proof : t -> bool
(** [can_open_proof x] check if [x] can start a proof, meaning it's either:
    - a sentence starting with: Theorem | Lemma | Fact | Remark | Property |
      Proposition | Corollary
    - a sentence starting with Goal (anonymous goal)
    - a definition with a proof
    - an Instance with a proof
    - a Function with a proof *)

val can_close_proof : t -> bool
(** [can_close_proof x] check if [x] can close a proof, meaning it's either Qed,
    Admitted, Abort or Abort all *)

open Raw_gen_args_converter

val get_extend_name : t -> extend_name option

val get_tactic_raw_generic_arguments :
  t -> Genarg.raw_generic_argument list option

val tactic_raw_generic_arguments_to_syntax_node :
  extend_name -> Genarg.raw_generic_argument list -> Code_point.t -> t option

val tacdef_body_list_to_syntax_node :
  Ltac_plugin.Tacexpr.tacdef_body list -> Code_point.t -> (t, Error.t) result

val raw_tactic_expr_to_syntax_node :
  Ltac_plugin.Tacexpr.raw_tactic_expr ->
  ?selector:Goal_select_view.t ->
  ?use_default:bool ->
  Code_point.t ->
  (t, Error.t) result

val raw_tactic_expr_to_syntax_node_in_state :
  token:Coq.Limits.Token.t ->
  st:Coq.State.t ->
  Ltac_plugin.Tacexpr.raw_tactic_expr ->
  ?selector:Goal_select_view.t ->
  ?use_default:bool ->
  Code_point.t ->
  (t, Error.t) result

val get_goal_selector_opt : t -> Goal_select_view.t option
val get_raw_tactic_expr : t -> Ltac_plugin.Tacexpr.raw_tactic_expr option

val get_raw_atomic_tactic_expr :
  t -> Ltac_plugin.Tacexpr.raw_atomic_tactic_expr option

val get_tacdef_bodies : t -> Ltac_plugin.Tacexpr.tacdef_body list option

val string_to_raw_tactic_expr :
  string -> (Ltac_plugin.Tacexpr.raw_tactic_expr, Error.t) result

val get_ltac_elements : t -> ltac_elements option
val drop_goal_selector : t -> t
val add_goal_selector : t -> Goal_select_view.t -> (t, Error.t) result
val is_auto : t -> bool
val is_assumption : t -> bool
val is_intros : t -> bool
val is_assert : t -> bool
val get_assert_expr : t -> Constrexpr.constr_expr option
val is_assert_by : t -> bool
val get_assert_by_raw_tac_expr : t -> Ltac_plugin.Tacexpr.raw_tactic_expr option

val apply_tac_then :
  t -> t -> ?start_point:Code_point.t -> unit -> (t, Error.t) result

val apply_tac_thens :
  t -> t list -> ?start_point:Code_point.t -> unit -> (t, Error.t) result
