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

let get_lemma_names (doc : Rocq_document.t) : (string list, Error.t) result =
  let ( let* ) = Result.bind in
  let* proofs = Rocq_document.get_proofs doc in

  Ok
    (List.filter_map
       (fun p -> Option.map Names.Id.to_string (Proof.get_proof_name p))
       proofs)

let pp_lemma_names (fmt : Format.formatter) (names : string list) : unit =
  Format.fprintf fmt "@[<hov>[%a]@]"
    (Format.pp_print_list
       ~pp_sep:(fun fmt () -> Format.fprintf fmt ";@ ")
       Format.pp_print_string)
    names

let lemma_names_to_json (names : string list) : Yojson.Safe.t =
  `List (List.map (fun name -> `String name) names)

type lemma = { name : string; axioms : string list }

let pp_lemma (fmt : Format.formatter) ({ name; axioms } : lemma) : unit =
  Format.fprintf fmt "@[<hov>{ name = %s;@ axioms = %a }@]" name pp_lemma_names
    axioms

let lemma_to_json ({ name; axioms } : lemma) : Yojson.Safe.t =
  `Assoc [ ("name", `String name); ("axioms", lemma_names_to_json axioms) ]

(* (\* parse "Print Assumptions lemma_name." for the used axioms *\) *)
(* let parse_print_assumptions (content : string) : (string list, Error.t) result = *)
(*   if String.equal content "Closed under the global context" then Ok [] *)
(*   else Ok [] *)

type printed_proof_term = { name : string; term : string }

let pp_printed_proof_term (fmt : Format.formatter)
    ({ name; term } : printed_proof_term) : unit =
  Format.fprintf fmt "@[<hov>{ name = %s;@ term = %s }@]" name term

let printed_proof_term_to_json ({ name; term } : printed_proof_term) :
    Yojson.Safe.t =
  `Assoc [ ("name", `String name); ("term", `String term) ]

let string_of_constr ~(token : Coq.Limits.Token.t) ~(st : Coq.State.t)
    (term : Constr.t) =
  Coq.State.in_state ~token ~st
    ~f:(fun () ->
      let env = Global.env () in
      let sigma = Evd.from_env env in
      Pp.string_of_ppcmds (Printer.pr_lconstr_env env sigma term))
    ()
  |> Error.protect_to_result

let get_proof_terms (doc : Rocq_document.t) :
    (printed_proof_term list, Error.t) result =
  let ( let* ) = Result.bind in
  let token = Coq.Limits.Token.create () in
  let* proofs = Rocq_document.get_proofs doc in
  let* proof_names_and_after_states =
    List.filter_map
      (fun (proof : Proof.t) ->
        let closing_node = proof.closing.node in
        let proof_name_opt =
          Option.map Names.Id.to_string (Proof.get_proof_name proof)
        in
        Option.map
          (fun proof_name ->
            let after_state = Runner.get_state_after doc closing_node token in
            match after_state with
            | Ok after_state -> Ok (proof_name, after_state)
            | Error err -> Error err)
          proof_name_opt)
      proofs
    |> List_utils.result_all
  in

  let* proof_tems =
    List_utils.map_result
      (fun (proof_name, after_state) ->
        let* global = Runner.resolve_global ~token after_state proof_name in
        let* constant =
          Proof_term.constant_of_global_ref global
          |> Option_utils.to_result
               ~none:
                 (Error.string_to_or_error
                    "Couldn't find an associated constant")
        in
        let* term_opt = Proof_term.get ~token after_state constant in
        let* term_repr =
          match term_opt with
          | Some term -> string_of_constr ~token ~st:after_state term
          | None -> Ok "NO TERM FOUND"
        in

        Ok { name = proof_name; term = term_repr })
      proof_names_and_after_states
  in

  Ok proof_tems

let get_lemma_and_assoc_axioms (doc : Rocq_document.t) :
    (lemma list, Error.t) result =
  let ( let* ) = Result.bind in
  let token = Coq.Limits.Token.create () in
  let* proofs = Rocq_document.get_proofs doc in

  let* proof_names_and_after_states =
    List.filter_map
      (fun (proof : Proof.t) ->
        let closing_node = proof.closing.node in
        let proof_name_opt =
          Option.map Names.Id.to_string (Proof.get_proof_name proof)
        in
        Option.map
          (fun proof_name ->
            let after_state = Runner.get_state_after doc closing_node token in
            match after_state with
            | Ok after_state -> Ok (closing_node, proof_name, after_state)
            | Error err -> Error err)
          proof_name_opt)
      proofs
    |> List_utils.result_all
  in

  let* _ =
    List_utils.map_result
      (fun ( (closing_node : Syntax_node.t),
             (proof_name : string),
             (state : Coq.State.t) ) ->
        let* command_node =
          Syntax_node.syntax_node_of_string
            ("Print Assumptions " ^ proof_name ^ ".")
            closing_node.range.end_
        in
        let diagnostics_err =
          Runner.run_node_with_diagnostics token state command_node
        in
        match diagnostics_err with
        | Ok (_, [ diag ]) ->
            let str_repr = Pp.string_of_ppcmds diag.message in
            Printf.eprintf "%s" str_repr;
            Ok str_repr
        | Ok (_, _) ->
            Error.string_to_or_error
              "Parsed more than a single diagnostic from Print assumptions."
        | Error (err, _) -> Error err)
      proof_names_and_after_states
  in

  Ok [ { name = "dummy"; axioms = [] } ]
