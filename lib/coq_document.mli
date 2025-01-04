open Proof
open Fleche
open Annotated_ast_node

type t = {
  filename : string;
  elements : annotatedASTNode list;
  document_repr : string;
}

type insertPosition = Before of int | After of int | Start | End

val parse_document : Doc.Node.t list -> string -> string -> t
val doc_to_yojson : t -> Yojson.Safe.t
val doc_of_yojson : Yojson.Safe.t -> t
val element_with_id_opt : int -> t -> annotatedASTNode option
val insert_node : annotatedASTNode -> t -> insertPosition -> (t, string) result
val remove_node_with_id : int -> t -> t
val get_proofs : t -> proof list
val dump_to_string : t -> string
val remove_proof : proof -> t -> t
val insert_proof : proof -> t -> insertPosition -> (t, string) result
val replace_proof : proof -> t -> (t, string) result
