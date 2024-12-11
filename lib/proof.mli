open Fleche
open Petanque
open Annotated_ast_node

(** Represents a proof in a Coq document. *)
type proof = {
  proposition : annotatedASTNode;
  proof_steps : annotatedASTNode list;
}
(** [proof] contains the initial proposition and a list of proof steps. *)

val get_names : Lang.Ast.Info.t list -> string list
(** A node can have multiple names (i.e., mutual recursive definitions) *)

val proof_to_coq_script_string : proof -> string
val get_proof_name : proof -> string option
val get_tactics : proof -> string list

type 'a nary_tree = Node of 'a * 'a nary_tree list

val get_proof_state : ('a, Agent.Error.t) result -> 'a

val count_goals : Coq.Limits.Token.t -> Agent.State.t -> int
(** Count the number of goals of a state *)

val print_tree : string nary_tree -> string -> unit

val tactics_with_goalcount :
  Coq.Limits.Token.t -> Agent.State.t -> string list -> (string * int) list

val treeify_proof : proof -> Doc.t -> string nary_tree
