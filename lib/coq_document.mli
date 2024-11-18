open Proof
open Fleche

type coq_element = CoqNode of Doc.Node.Ast.t | CoqStatement of proof

val parse_document : Doc.Node.Ast.t list -> coq_element list
val coq_element_to_string : coq_element -> string
