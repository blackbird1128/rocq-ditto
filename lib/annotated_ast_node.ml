open Fleche

type annotatedASTNode = {
  ast : Doc.Node.Ast.t;
  range : Lang.Range.t;
  repr : string;
}

let is_doc_node_ast_tactic (x : annotatedASTNode) : bool =
  match (Coq.Ast.to_coq x.ast.v).CAst.v.expr with
  | VernacSynterp synterp_expr -> (
      match synterp_expr with
      | VernacExtend (ext, _) ->
          if ext.ext_plugin = "coq-core.plugins.ltac" then true else false
      | _ -> false)
  | VernacSynPure _ -> false

let is_doc_node_ast_proof_start (x : annotatedASTNode) : bool =
  match (Coq.Ast.to_coq x.ast.v).CAst.v.expr with
  | VernacSynterp _ -> false
  | VernacSynPure expr -> (
      match expr with
      | Vernacexpr.VernacStartTheoremProof _ -> true
      | _ -> false)

let is_doc_node_ast_proof_end (x : annotatedASTNode) : bool =
  match (Coq.Ast.to_coq x.ast.v).CAst.v.expr with
  | VernacSynterp _ -> false
  | VernacSynPure expr -> (
      match expr with Vernacexpr.VernacEndProof _ -> true | _ -> false)
