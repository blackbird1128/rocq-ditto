open Nary_tree

type proof_tree = Syntax_node.t nary_tree

val apply_transformation_step :
  Transforming_step.t -> proof_tree -> (proof_tree, Error.t) result
