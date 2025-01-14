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

val get_proof_state :
  Agent.State.t Agent.Run_result.t Agent.R.t -> Agent.State.t

val count_goals : Coq.Limits.Token.t -> Agent.State.t -> int
(** Count the number of goals of a state *)

val print_tree : annotatedASTNode nary_tree -> string -> unit

val get_init_state :
  Doc.t -> proof -> Agent.State.t Agent.Run_result.t Agent.R.t option

val proof_steps_with_goalcount :
  Coq.Limits.Token.t ->
  Agent.State.t ->
  annotatedASTNode list ->
  (annotatedASTNode * int) list

val treeify_proof : Doc.t -> proof -> annotatedASTNode nary_tree
val tree_to_proof : annotatedASTNode nary_tree -> proof
val last_offset : proof -> int
val proof_nodes : proof -> annotatedASTNode list
val proof_from_nodes : annotatedASTNode list -> proof
