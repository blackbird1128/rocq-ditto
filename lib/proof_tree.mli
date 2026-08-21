type proof_tree = Syntax_node.t Nary_tree.t

val apply_transformation_step :
  Transforming_step.t -> proof_tree -> (proof_tree, Error.t) result

val proof_tree_from_parents :
  int * Syntax_node.t ->
  (int * Syntax_node.t, int * Syntax_node.t) Hashtbl.t ->
  Syntax_node.t Nary_tree.t

val tree_to_proof : Syntax_node.t Nary_tree.t -> (Proof.t, Error.t) result

val treeify_proof :
  Rocq_document.t -> Proof.t -> (Syntax_node.t Nary_tree.t, Error.t) result
