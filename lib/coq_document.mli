open Proof
open Fleche
open Annotated_ast_node

type t = {
  filename : string;
  elements : annotatedASTNode list;
  document_repr : string;
}

val parse_document : Doc.Node.t list -> string -> string -> t
val remove_node_with_id : int -> t -> t
val get_proofs : t -> proof list
val dump_to_string : t -> string
