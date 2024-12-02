open Proof
open Fleche

type coq_element = CoqNode of Doc.Node.Ast.t | CoqStatement of proof

let coq_element_to_string (x : coq_element) : string =
  match x with
  | CoqNode e -> Ppvernac.pr_vernac (Coq.Ast.to_coq e.v) |> Pp.string_of_ppcmds
  | CoqStatement e -> Proof.proof_to_coq_script_string e

let get_theorem_names (elements : coq_element list) : string list =
  List.map
    (fun x ->
      match x with
      | CoqStatement e -> Option.default "" (Proof.get_proof_name e)
      | _ -> "")
    elements
  |> List.filter (fun s -> String.length s > 0)

let get_proofs (elements : coq_element list) : proof list =
  List.filter_map
    (fun x -> match x with CoqStatement e -> Some e | _ -> None)
    elements

let parse_document (x : Doc.Node.Ast.t list) : coq_element list =
  let rec aux spans current_proof document =
    match spans with
    | [] -> (
        match current_proof with
        | Some _ ->
            raise (Invalid_argument "proof started but ended at document end")
        | None -> List.rev document)
    | span :: rest -> (
        if is_doc_node_ast_proof_start span then
          aux rest (Some { proposition = span; proof_steps = [] }) document
        else if is_doc_node_ast_proof_end span then
          match current_proof with
          | Some current_proof ->
              let completed_proof =
                {
                  current_proof with
                  proof_steps = List.rev (span :: current_proof.proof_steps);
                }
              in
              aux rest None (CoqStatement completed_proof :: document)
          | None -> raise (Invalid_argument "proof ended but never started")
        else
          match current_proof with
          | Some proof ->
              aux rest
                (Some { proof with proof_steps = span :: proof.proof_steps })
                document
          | None -> aux rest None (CoqNode span :: document))
    (* Skip spans not part of any proof *)
  in
  aux x None []

(*
   let get_document_script (d : coq_element list) : string =
     String.concat "\n"
       (List.map
          (fun x -> match (x : coq_element) with CoqNode e -> Ppvernac.pr_vernac x. | CoqStatement p -> "")
   (*   Ppvernac.pr_vernac (Coq.Ast.to_coq *)
   (*   |> Pp.string_of_ppcmds |> print_endline) *)
          d) *)
