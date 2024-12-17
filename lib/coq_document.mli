open Proof
open Fleche
open Annotated_ast_node

type coq_element = CoqNode of annotatedASTNode | CoqStatement of proof

type t = {
  filename : string;
  elements : coq_element list;
  document_repr : string;
}

val parse_document : Doc.Node.t list -> string -> string -> t
val coq_element_to_string : coq_element -> string
val get_theorem_names : t -> string list
val get_proofs : t -> proof list
val replace_coq_element : coq_element -> t -> t
val dump_to_string : t -> string
