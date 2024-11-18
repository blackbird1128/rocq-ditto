open Fleche

type proof = { proposition : Doc.Node.Ast.t; proof_steps : Doc.Node.Ast.t list }
(* proposition can also be a type, better name ? *)

let is_doc_node_ast_tactic (x : Doc.Node.Ast.t) : bool =
  match (Coq.Ast.to_coq x.v).CAst.v.expr with
  | VernacSynterp synterp_expr -> (
      match synterp_expr with
      | VernacExtend (extend_name, _) ->
          print_endline extend_name.Vernacexpr.ext_plugin;
          false
      | _ -> false)
  | VernacSynPure _ -> false

let is_doc_node_ast_proof_start (x : Doc.Node.Ast.t) : bool =
  match (Coq.Ast.to_coq x.v).CAst.v.expr with
  | VernacSynterp _ -> false
  | VernacSynPure expr -> (
      match expr with
      | Vernacexpr.VernacStartTheoremProof _ -> true
      | _ -> false)

let is_doc_node_ast_proof_end (x : Doc.Node.Ast.t) : bool =
  match (Coq.Ast.to_coq x.v).CAst.v.expr with
  | VernacSynterp _ -> false
  | VernacSynPure expr -> (
      match expr with Vernacexpr.VernacEndProof _ -> true | _ -> false)

let get_proofs (x : Doc.Node.Ast.t list) : proof list =
  let rec aux spans current_proof proofs =
    match spans with
    | [] -> (
        match current_proof with
        | Some _ ->
            raise (Invalid_argument "proof started but ended at document end")
        | None -> List.rev proofs)
    | span :: rest -> (
        if is_doc_node_ast_proof_start span then
          aux rest (Some { proposition = span; proof_steps = [] }) proofs
        else if is_doc_node_ast_proof_end span then
          match current_proof with
          | Some current_proof ->
              let completed_proof =
                {
                  current_proof with
                  proof_steps = List.rev (span :: current_proof.proof_steps);
                }
              in
              aux rest None (completed_proof :: proofs)
          | None -> raise (Invalid_argument "proof ended but never started")
        else
          match current_proof with
          | Some proof ->
              aux rest
                (Some { proof with proof_steps = span :: proof.proof_steps })
                proofs
          | None -> aux rest None proofs)
    (* Skip spans not part of any proof *)
  in
  aux x None []
