open Fleche
open Syntax_node
open Proof_tree

type proof_status = Admitted | Proved | Aborted

val pp_proof_status : Format.formatter -> proof_status -> unit

type transformation_step =
  | Remove of int
  | Replace of int * syntaxNode
  | Add of syntaxNode

val pp_transformation_step : Format.formatter -> transformation_step -> unit
val print_transformation_step : transformation_step -> unit

type proof = {
  proposition : syntaxNode;
  proof_steps : syntaxNode list;
  status : proof_status;
}
(** Represents a proof in a Coq document. [proof] contains the initial
    proposition and a list of proof steps. *)

val get_names : syntaxNode -> string list
(** Get the names of a node. A node can have multiple names (i.e., mutual
    recursive definitions) *)

val get_proof_name : proof -> string option
(** Retrieve the name of the proof's proposition if available.
    [get_proof_name p] returns [Some name] if the proof [p] has a proposition
    with a name, otherwise it returns [None]. *)

val get_proof_status : proof -> proof_status option

val proof_status_from_last_node : syntaxNode -> (proof_status, string) result
(** Get the proof status of the last node of a proof or an error if the node
    isn't a closing node. If the proof was proved, return [Proved], if the proof
    is admitted, return [Admitted], and if the proof was aborted with Abort or
    Abort All, return [Aborted] otherwise, return an error. *)

val print_proof : proof -> unit

val print_tree : syntaxNode nary_tree -> string -> unit
(** Print a tree structure with indentation. [print_tree tree indent] prints a
    tree, where [tree] is an [syntaxNode nary_tree] and [indent] is a string
    used for indentation to represent the tree structure visually. *)

val proof_nodes : proof -> syntaxNode list
(** Extracts the nodes from a proof. [proof_nodes p] returns a list containing
    the proposition of the proof [p] followed by its proof steps. *)

val proof_from_nodes : syntaxNode list -> (proof, string) result
(** Create a proof from a list of annotated AST nodes. [proof_from_nodes nodes]
    takes a list of nodes and returns a proof where the first node in the list
    is used as the proposition, and the remaining nodes are the proof steps. If
    the list made of less than three nodes or the last node isn't a valid proof
    end, return an error. *)
