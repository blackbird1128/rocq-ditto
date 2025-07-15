open Nary_tree
open Syntax_node
open Proof

type proof_tree = syntaxNode nary_tree

val apply_transformation_step :
  transformation_step -> proof_tree -> (proof_tree, Error.t) result
