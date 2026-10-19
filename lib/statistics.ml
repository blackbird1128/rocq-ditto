type 'a scoped_statistic =
  | ProofScope of (Rocq_document.t -> Proof.t -> ('a, Error.t) result)
  | DocScope of (Rocq_document.t -> ('a, Error.t) result)

type 'a t = {
  name : string;
  scope : 'a scoped_statistic;
  empty : 'a;
  combine : 'a -> 'a -> 'a;
  pp : Format.formatter -> 'a -> unit;
  to_json : 'a -> Yojson.Safe.t;
}

type packed = Statistic : 'a t -> packed

let run (doc : Rocq_document.t) (statistic : 'a t) : ('a, Error.t) result =
  let ( let* ) = Result.bind in
  match statistic.scope with
  | ProofScope compute ->
      let* proofs = Rocq_document.get_proofs doc in
      List_utils.fold_left_result
        (fun acc p ->
          let* compute_res = compute doc p in
          Ok (statistic.combine acc compute_res))
        statistic.empty proofs
  | DocScope compute -> compute doc

let count_induction_calls_in_tacexpr (x : Ltac_plugin.Tacexpr.raw_tactic_expr) :
    int =
  Tacexpr_map.tacexpr_fold
    (fun acc expr ->
      match expr.v with
      | Ltac_plugin.Tacexpr.TacAtom
          (Ltac_plugin.Tacexpr.TacInductionDestruct (true, false, _)) ->
          acc + 1
      | _ -> acc)
    0 x

let count_induction (doc : Rocq_document.t) : (int, Error.t) result =
  let nodes = doc.elements in
  Ok
    (List.fold_left
       (fun acc node ->
         match Syntax_node.get_raw_tactic_expr node with
         | Some expr -> acc + count_induction_calls_in_tacexpr expr
         | None -> acc)
       0 nodes)

type proof_status_count = { proved : int; admitted : int }

let pp_proof_status_count (fmt : Format.formatter) { proved; admitted } : unit =
  Format.fprintf fmt "proved: %d; admitted: %d" proved admitted

let proof_status_count_to_json { proved; admitted } : Yojson.Safe.t =
  `Assoc [ ("proved", `Int proved); ("admitted", `Int admitted) ]

let count_proof_status (doc : Rocq_document.t) :
    (proof_status_count, Error.t) result =
  let ( let* ) = Result.bind in
  let* proofs = Rocq_document.get_proofs doc in

  let statuses = List.map (fun proof -> Proof.status proof) proofs in

  let proved =
    List_utils.count (fun status -> status = Proof.Proved) statuses
  in
  let admitted =
    List_utils.count (fun status -> status = Proof.Admitted) statuses
  in

  Ok { proved; admitted }

let add_proof_status_count (a : proof_status_count) (b : proof_status_count) :
    proof_status_count =
  { proved = a.proved + b.proved; admitted = a.admitted + b.admitted }
