open Fleche

type proof = { proposition : Doc.Node.Ast.t; proof_steps : Doc.Node.Ast.t list }
(* proposition can also be a type, better name ? *)

(* A node can have multiple names (ie mutual recursive defs) *)
let get_names (infos : Lang.Ast.Info.t list) =
  List.concat_map
    (fun (info : Lang.Ast.Info.t) ->
      match info.name.v with None -> [] | Some s -> [ s ])
    infos

let get_proof_name (p : proof) : string option =
  if Option.has_some p.proposition.ast_info then
    (Option.get p.proposition.ast_info |> get_names |> List.nth_opt) 0
  else None

let doc_node_to_string (d : Doc.Node.Ast.t) : string =
  Ppvernac.pr_vernac (Coq.Ast.to_coq d.v) |> Pp.string_of_ppcmds

let proof_to_coq_script_string (p : proof) : string =
  doc_node_to_string p.proposition
  ^ "\n"
  ^ String.concat "\n" (List.map (fun n -> doc_node_to_string n) p.proof_steps)

let is_doc_node_ast_tactic (x : Doc.Node.Ast.t) : bool =
  match (Coq.Ast.to_coq x.v).CAst.v.expr with
  | VernacSynterp synterp_expr -> (
      match synterp_expr with VernacExtend (_, _) -> false | _ -> false)
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
