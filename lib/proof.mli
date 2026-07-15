type proof_status = Admitted | Proved | Aborted
[@@deriving show { with_path = false }]

val pp_proof_status : Format.formatter -> proof_status -> unit

type attach_position = LineAfter | LineBefore | SameLine
[@@deriving show { with_path = false }]

type transformation_step =
  | Remove of Uuidm.t
  | Replace of Uuidm.t * Syntax_node.t
  | Add of Syntax_node.t
  | Attach of Syntax_node.t * attach_position * Uuidm.t

val pp_transformation_step : Format.formatter -> transformation_step -> unit
val transformation_step_to_string : transformation_step -> string

type t = private {
  proposition : Syntax_node.t;
  proof_steps : Syntax_node.t list;
}
(** Represents a proof in a Coq document. [proof] contains the initial
    proposition and a list of proof steps. *)

val get_theorem_kind : t -> Decls.theorem_kind option
(** Get the theorem kind of a proof. If the proof isn't a basic assertion
    command ie: Theorem, Lemma, Fact, Remark, Property, Proposition or
    Corollary, return [None], otherwise return the kind of the theorem. *)

val get_constr_expr : t -> Constrexpr.constr_expr option
(** Get the constr_expr of the proof. If the proof start a theorem or a proof
    (as it should) return the [Constrexpr.constr_expr] representing the
    expression stated by the proof or theorem, otherwise return [None] *)

type theorem_components = {
  kind : Decls.theorem_kind;
  name : Names.lident;
  universe : Constrexpr.universe_decl_expr option;
  binders : Constrexpr.local_binder_expr list;
  expr : Constrexpr.constr_expr;
}

val get_theorem_components : t -> theorem_components option

val syntax_node_of_theorem_components :
  theorem_components -> Code_point.t -> Syntax_node.t

val syntax_node_of_theorem_components_in_state :
  token:Coq.Limits.Token.t ->
  st:Coq.State.t ->
  theorem_components ->
  Code_point.t ->
  (Syntax_node.t, Error.t) result

val get_proof_name : t -> string option
(** Retrieve the name of the proof's proposition if available.
    [get_proof_name p] returns [Some name] if the proof [p] has a proposition
    with a name, otherwise it returns [None]. *)

val status : t -> proof_status
(** Get the proof status of a proof. [status proof] returns a [proof_status]
    matching the status of the last node of the proof. Returns [Aborted] for
    both [Abort] and [Abort All]. *)

val get_proof_conclusion : t -> Constrexpr.constr_expr option

val map_proof_proposition :
  (Constrexpr.constr_expr -> Constrexpr.constr_expr) ->
  t ->
  transformation_step option

val map_proof_proposition_in_state :
  (Constrexpr.constr_expr -> Constrexpr.constr_expr) ->
  token:Coq.Limits.Token.t ->
  st:Coq.State.t ->
  t ->
  (transformation_step option, Error.t) result

val proof_nodes : t -> Syntax_node.t list
(** Extracts the nodes from a proof. [proof_nodes p] returns a list containing
    the proposition of the proof [p] followed by its proof steps. *)

val proof_from_nodes : Syntax_node.t list -> (t, Error.t) result
(** Create a proof from a list of annotated AST nodes. [proof_from_nodes nodes]
    takes a list of nodes and returns a proof where the first node in the list
    is used as the proposition, and the remaining nodes are the proof steps. If
    the list made of less than two nodes, the first node can't open a proof or
    the last node isn't a valid proof end, return an error. *)
