open Proof
open Fleche
open Syntax_node

type t = {
  filename : string;
  elements : syntaxNode list;
  document_repr : string;
}

type shiftMethod = ShiftVertically | ShiftHorizontally

val pp_coq_document : Format.formatter -> t -> unit

val parse_document : Doc.Node.t list -> string -> string -> t
(** Parse a document represented as a list of nodes and a string.
    [parse_document nodes document_repr filename] returns a parsed
    representation of the document, annotating proof with an unique id for each
    proofs.

    The function raises an [Invalid_argument] exception if a proof span ends
    without a corresponding start or if a proof starts but ends at the end of
    the document. *)

val doc_to_yojson : t -> Yojson.Safe.t
(** Convert a document of type [t] into a [Yojson.Safe.t] object. *)

val doc_of_yojson : Yojson.Safe.t -> t
(** Convert a JSON representation into a document of type [t]. *)

val element_with_id_opt : int -> t -> syntaxNode option
(** Find an element with a specific ID in a document.
    [element_with_id_opt element_id doc] returns [Some element] if an element
    with the given [element_id] exists in the document [doc], otherwise it
    returns [None]. *)

val remove_node_with_id : int -> t -> t
(** Remove a node with a specific ID from the document.
    [remove_node_with_id target_id doc] removes the element with the given
    [target_id] from the document [doc]. If the element is found, it returns a
    new document with the element removed, potentially adjusting the line
    numbers of subsequent elements. If the element is not found, it returns the
    original document. *)

val colliding_nodes : syntaxNode -> t -> syntaxNode list
(** return the nodes colliding with target node *)

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

val get_proofs : t -> proof list
(** Extract proofs from a document. [get_proofs doc] takes a document [doc] of
    type [t] and returns a list of proofs. Each proof is constructed by
    aggregating elements of the document that share the same proof identifier.
*)

val dump_to_string : t -> string
(** Convert an annotated document to a string representation.
    [dump_to_string doc] returns a string that represents the structure of the
    annotated document [doc], formatting the nodes according to their positions
    and characters in the document. *)

val remove_proof : proof -> t -> t
(** Remove a proof from the document. [remove_proof target doc] removes all
    nodes associated with the given [target] proof from the [doc]. *)

val insert_proof : proof -> t -> (t, string) result
(** Insert a proof into a document at a specified position.
    [insert_proof target doc insert_pos] takes a [target] proof, a document
    [doc], and an insertion position [insert_pos]. It returns [Ok doc_acc] with
    the modified document if the insertion is successful, or [Error msg] with an
    error message if it fails. *)

val replace_proof : proof -> t -> (t, string) result
(** Replace a proof in a document. [replace_proof target doc] attempts to find a
    proof corresponding to [target.proposition.id] in [doc]. If found, it
    removes this proof and inserts [target] at the appropriate position. If the
    proof is not found, it returns an error indicating that the proof with the
    specified id is not in the document. *)
