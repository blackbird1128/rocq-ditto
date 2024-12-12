open Proof
open Fleche
open Annotated_ast_node

type coq_element = CoqNode of annotatedASTNode | CoqStatement of proof

val parse_document : Doc.Node.t list -> string -> coq_element list
val coq_element_to_string : coq_element -> string
val get_theorem_names : coq_element list -> string list
val get_proofs : coq_element list -> proof list
val replace_coq_element : coq_element -> coq_element list -> coq_element list

val dump_to_string : coq_element list -> string
