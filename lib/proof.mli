open Fleche
open Petanque
open Annotated_ast_node
open Proof_tree

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
(* val get_tactics : proof -> string list *)

val get_proof_state : ('a, Agent.Error.t) result -> 'a

val count_goals : Coq.Limits.Token.t -> Agent.State.t -> int
(** Count the number of goals of a state *)

val print_tree : annotatedASTNode nary_tree -> string -> unit

val proof_steps_with_goalcount :
  Coq.Limits.Token.t ->
  Agent.State.t ->
  annotatedASTNode list ->
  (annotatedASTNode * int) list

val treeify_proof : proof -> Doc.t -> annotatedASTNode nary_tree
val last_offset : proof -> int
val proof_nodes : proof -> annotatedASTNode list
