open Proof
open Fleche
open Syntax_node

type t = {
  id_counter : Unique_id.counter;
  filename : string;
  elements : syntaxNode list;
  document_repr : string;
  initial_state : Coq.State.t;
}

type removeMethod = LeaveBlank | ShiftNode
type shiftMethod = ShiftVertically | ShiftHorizontally

val pp_coq_document : Format.formatter -> t -> unit
val parse_document : Doc.t -> t

val element_with_id_opt : int -> t -> syntaxNode option
(** Find an element with a specific ID in a document.
    [element_with_id_opt element_id doc] returns [Some element] if an element
    with the given [element_id] exists in the document [doc], otherwise it
    returns [None]. *)

val colliding_nodes : syntaxNode -> t -> syntaxNode list
(** return the nodes colliding with target node *)

val compare_nodes : syntaxNode -> syntaxNode -> int
val split_at_id : int -> t -> syntaxNode list * syntaxNode list

val remove_node_with_id :
  int -> ?remove_method:removeMethod -> t -> (t, string) result
(** Remove a node with a specific ID from the document.
    [remove_node_with_id target_id doc] removes the element with the given
    [target_id] from the document [doc]. If the element is found, it returns a
    new document with the element removed wrapped in [Ok], potentially adjusting
    the line numbers of subsequent elements. If the element is not found, it
    returns an Error indicating that the element wasn't found. *)

val insert_node :
  syntaxNode -> ?shift_method:shiftMethod -> t -> (t, string) result
(** [insert_node new_node doc insert_pos] attempts to insert [new_node] into the
    document [doc] at the position specified by [insert_pos]. The insertion can
    occur before or after a node identified by [id], or at the start or end of
    the document.

    Returns [Ok new_doc] if the insertion is successful, where [new_doc] is the
    updated document. If the target node with the specified [id] does not exist,
    it returns an [Error] with a message indicating the failure.

    The possible insertion positions are:
    - [Before id]: inserts [new_node] before the node with the given [id].
    - [After id]: inserts [new_node] after the node with the given [id].
    - [Start]: inserts [new_node] at the start of the document.
    - [End]: appends [new_node] to the end of the document. *)

val replace_node : int -> syntaxNode -> t -> (t, string) result

val get_proofs : t -> (proof list, string) result
(** Extract proofs from a document. [get_proofs doc] takes a document [doc] of
    type [t] and returns a list of proofs. Each proof is constructed by
    aggregating elements of the document that share the same proof identifier.
*)

val dump_to_string : t -> string
(** Convert an annotated document to a string representation.
    [dump_to_string doc] returns a string that represents the structure of the
    annotated document [doc], formatting the nodes according to their positions
    and characters in the document. *)

val apply_transformation_step : transformation_step -> t -> (t, string) result

val apply_transformations_steps :
  transformation_step list -> t -> (t, string) result
