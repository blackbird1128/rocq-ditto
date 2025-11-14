open Syntax_node
open Proof

let constructivize_doc (doc : Rocq_document.t) :
    (transformation_step list, Error.t) result =
  Ok []
