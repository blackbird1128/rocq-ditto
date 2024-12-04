open Fleche
open Petanque

(** Represents a proof in a Coq document. *)
type proof = { proposition : Doc.Node.Ast.t; proof_steps : Doc.Node.Ast.t list }
(** [proof] contains the initial proposition and a list of proof steps. *)

val get_names : Lang.Ast.Info.t list -> string list
(** A node can have multiple names (i.e., mutual recursive definitions) *)

val proof_to_coq_script_string : proof -> string
val get_proof_name : proof -> string option

val is_doc_node_ast_tactic : Doc.Node.Ast.t -> bool
(** [is_doc_node_ast_tactic x] checks if [x] represents a tactic in the Coq document. *)

val is_doc_node_ast_proof_start : Doc.Node.Ast.t -> bool
(** [is_doc_node_ast_proof_start x] checks if [x] marks the start of a proof in the Coq document. *)

val is_doc_node_ast_proof_end : Doc.Node.Ast.t -> bool
(** [is_doc_node_ast_proof_end x] checks if [x] marks the end of a proof in the Coq document. *)

val get_tactics : proof -> string list

type 'a nary_tree = Node of 'a * 'a nary_tree list

val get_proof_state : ('a, Agent.Error.t) result -> 'a

val count_goals : Coq.Limits.Token.t -> Agent.State.t -> int
(** Count the number of goals of a state *)

val print_tree : string nary_tree -> string -> unit

val tactics_with_goalcount :
  Coq.Limits.Token.t -> Agent.State.t -> string list -> (string * int) list

val treeify_proof : proof -> Doc.t -> string nary_tree
