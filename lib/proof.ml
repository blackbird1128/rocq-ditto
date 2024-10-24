open CoqDocument

type proof = { proposition : rangedCoqSpan; proof_steps : rangedCoqSpan list }
(* proposition can also be a type, better name ? *)

let is_ranged_coq_span_proof_start (x : rangedCoqSpan) : bool =
  if Option.has_some x.span then
    let x_span = Option.get x.span in
    match x_span.CAst.v.expr with
    | VernacSynterp synterp_expr -> false
    | VernacSynPure expr -> (
        match expr with
        | Vernacexpr.VernacStartTheoremProof _ -> true
        | _ -> false)
  else false

let is_ranged_coq_span_proof_end (x : rangedCoqSpan) : bool =
  if Option.has_some x.span then
    let x_span = Option.get x.span in
    match x_span.CAst.v.expr with
    | VernacSynterp synterp_expr -> false
    | VernacSynPure expr -> (
        match expr with Vernacexpr.VernacEndProof _ -> true | _ -> false)
  else false

let get_proofs (x : coqDocument) : proof list =
  let rec aux spans current_proof proofs =
    match spans with
    | [] -> (
        match current_proof with
        | Some proof ->
            raise (Invalid_argument "proof started but ended at document end")
        | None -> List.rev proofs)
    | span :: rest -> (
        if is_ranged_coq_span_proof_start span then
          aux rest (Some { proposition = span; proof_steps = [] }) proofs
        else if is_ranged_coq_span_proof_end span then
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
  aux x.spans None []
