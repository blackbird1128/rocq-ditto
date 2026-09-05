open Fleche
open Ditto
open Ditto.Proof
open Ditto_cli_lib.Cli

type scoped_function =
  | ProofScope of
      (Rocq_document.t -> Proof.t -> (Transforming_step.t list, Error.t) result)
  | DocScope of (Rocq_document.t -> (Transforming_step.t list, Error.t) result)

type 'a scoped_statistic =
  | ProofScope of (Rocq_document.t -> Proof.t -> ('a, Error.t) result)
  | DocScope of (Rocq_document.t -> ('a, Error.t) result)

type 'a statistic = {
  name : string;
  scope : 'a scoped_statistic;
  empty : 'a;
  combine : 'a -> 'a -> 'a;
  pp : Format.formatter -> 'a -> unit;
  to_json : 'a -> Yojson.Safe.t;
}

let run_statistic (doc : Rocq_document.t) (statistic : 'a statistic) :
    ('a, Error.t) result =
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

let print_induction_count (formatter : Format.formatter) (count : int) =
  Format.fprintf formatter "induction count: %s" (string_of_int count)

let induction_count_to_json (count : int) : Yojson.Safe.t =
  `Assoc [ ("count", `Int count) ]

let statistic_kind_to_statistic (kind : statistic_kind) : 'a statistic =
  match kind with
  | CountInduction ->
      {
        name = "count induction";
        scope = DocScope Statistics.count_induction;
        empty = 0;
        combine = ( + );
        pp = print_induction_count;
        to_json = induction_count_to_json;
      }

let wrap_to_treeify (doc : Rocq_document.t) (x : Proof.t) :
    (Syntax_node.t Nary_tree.t, Error.t) result =
  Proof_tree.treeify_proof doc x

let transformation_kind_to_scoped_function (kind : transformation_kind) :
    scoped_function =
  let ( let* ) = Result.bind in
  match kind with
  | RenameDefinition -> DocScope Transformations.rename_definition
  | ExplicitFreshVariables ->
      ProofScope Transformations.explicit_fresh_variables
  | TurnIntoOneliner ->
      ProofScope
        (fun doc x ->
          let* proof_tree = wrap_to_treeify doc x in
          Transformations.turn_into_oneliner doc proof_tree)
  | ReplaceAutoWithSteps -> ProofScope Transformations.replace_auto_with_steps
  | CompressIntro -> ProofScope Transformations.compress_intro
  | FlattenGoalSelectors -> ProofScope Transformations.flatten_goal_selectors
  | ExplicitIdentInIntro -> ProofScope Transformations.name_identifier_in_intro
  | ExplicitApply -> ProofScope Transformations.explicit_apply
  | ReplaceInductionWithDestruct ->
      ProofScope Transformations.replace_induction_by_destruct_when_possible
  | AddProofNodeIfMissing ->
      ProofScope Transformations.add_proof_node_if_missing
  | RemoveProofWith -> ProofScope Transformations.remove_proof_with
  | ConstructiviseGeocoq -> DocScope Constructivisation.constructivise_doc
  | RocqToLean -> DocScope Rocq_to_lean.rocq_to_lean
  | IdProofTransformation -> ProofScope Transformations.id_transform
  | IdDocTransformation -> DocScope (fun _ -> Ok [])

let local_apply_doc_transformation (doc_acc : Rocq_document.t)
    (trans : Rocq_document.t -> (Transforming_step.t list, Error.t) result) :
    (Rocq_document.t, Error.t) result =
  Transformations.apply_doc_transformation trans doc_acc

let print_current_running (proof_count : int) (proof_total : int)
    (proof_name : string) (transformation_kind : transformation_kind)
    (verbosity : verbosity) =
  match verbosity with
  | Verbose ->
      Printf.printf "Running transformation %s on %-20s (%d/%d)%!\n%!"
        (transformation_kind_to_string transformation_kind)
        proof_name (proof_count + 1) proof_total
  | Normal ->
      Printf.printf "\027[2K\rRunning transformation %s on %-20s(%d/%d)%!"
        (transformation_kind_to_string transformation_kind)
        proof_name (proof_count + 1) proof_total
  | Quiet -> ()

let apply_steps
    (transformation_steps : (Transforming_step.t list, Error.t) result)
    (curr_doc : Rocq_document.t) (proof_count : int) (proof : 'a) =
  match transformation_steps with
  | Ok steps ->
      ( Rocq_document.apply_transformations_steps steps curr_doc,
        proof_count + 1,
        curr_doc,
        Some proof )
  | Error err -> (Error err, proof_count, curr_doc, Some proof)

let display_transformation_error (prev_proof : Proof.t option)
    (transformation_kind : transformation_kind) (err : Error.t) =
  let prev_proof_name =
    match prev_proof with
    | Some prev_proof ->
        Option.default "anonymous"
          (Proof.get_proof_name prev_proof |> Option.map Names.Id.to_string)
    | None -> "None"
  in
  let transformation_name = transformation_kind_to_string transformation_kind in

  Printf.eprintf
    "Error when running the transformation %s on %s, canceling it\nError: %s%!"
    transformation_name prev_proof_name (Error.to_string_hum err)

let local_apply_proof_transformation (doc_acc : Rocq_document.t)
    (transformation :
      Rocq_document.t -> Proof.t -> (Transforming_step.t list, Error.t) result)
    (transformation_kind : transformation_kind) (proof_list : Proof.t list)
    (verbosity : verbosity) : Rocq_document.t =
  let proof_total = List.length proof_list in
  let first_proof = List_utils.head_opt proof_list in
  let token = Coq.Limits.Token.create () in
  let res, _, _, prev_proof =
    List.fold_left
      (fun (doc_acc_bis, proof_count, prev_doc, (prev_proof : Proof.t option))
           proof ->
        let curr_doc =
          match doc_acc_bis with
          | Ok curr_doc -> curr_doc
          | Error err ->
              display_transformation_error prev_proof transformation_kind err;
              prev_doc
        in

        let status_before =
          Runner.get_init_state curr_doc proof.opening token
        in
        let proof_name =
          Option.default "anonymous"
            (Proof.get_proof_name proof |> Option.map Names.Id.to_string)
        in
        print_current_running proof_count proof_total proof_name
          transformation_kind verbosity;
        match status_before with
        | Ok _ ->
            let transformation_steps = transformation curr_doc proof in
            apply_steps transformation_steps curr_doc proof_count proof
        | Error _ ->
            let prev_proof_name =
              Option.map
                (fun p ->
                  Proof.get_proof_name p |> Option.map Names.Id.to_string)
                prev_proof
              |> Option.flatten
              |> Option.default "No previous proof ? This might be a bug\n"
            in
            Printf.printf
              "Invalid state after transforming proof %s, canceling it \n"
              prev_proof_name;
            let transformation_steps = transformation prev_doc proof in
            apply_steps transformation_steps prev_doc proof_count proof)
      (Ok doc_acc, 0, doc_acc, first_proof)
      proof_list
  in
  match res with
  | Ok res -> res
  | Error err ->
      display_transformation_error prev_proof transformation_kind err;
      doc_acc

let print_info (filename : string) (verbosity : verbosity) : unit =
  Printf.printf "\nAll transformations applied, writing to file %s\n%!" filename;

  match verbosity with
  | Verbose ->
      let stats = Stats.Global.dump () in
      Printf.printf "rocq-ditto stats: %s\n" (Stats.Global.to_string stats);
      Printf.printf "rocq-ditto %s\n" (Memo.GlobalCacheStats.stats ())
  | _ -> ()

let statistic_action (doc : Fleche.Doc.t) (config : statistic_configuration) =
  let ( let* ) = Result.bind in

  let* parsed_doc = Rocq_document.parse_document doc in

  if config.format = Text then
    Printf.printf "applying statistic : %s\n"
      (statistic_kind_to_string config.statistic_kind);

  let statistic = statistic_kind_to_statistic config.statistic_kind in
  let* value = run_statistic parsed_doc statistic in
  (match config.format with
  | Text -> Format.printf "%a@." statistic.pp value
  | Json ->
      Format.printf "%a@."
        (Yojson.Safe.pretty_print ~std:false)
        (statistic.to_json value));
  Ok ()

let save_vo_to_file (filename : string) (doc : Rocq_document.t)
    (doc_uri : Lang.LUri.File.t) (token : Coq.Limits.Token.t) :
    (unit, Error.t) result =
  let ( let* ) = Result.bind in
  Printf.printf "Saving vo: ";
  let* uri =
    Lang.LUri.of_string filename
    |> Lang.LUri.File.of_uri
    |> Result.map_error Error.of_string
  in

  let ldir = Coq.Workspace.dirpath_of_uri ~uri:doc_uri in
  let in_file = Lang.LUri.File.to_string_file uri in
  let* state =
    match List_utils.last doc.elements with
    | Some last ->
        let* st = Runner.get_init_state doc last token in
        Runner.run_node token st last
    | None -> Ok doc.root_state
  in

  let res =
    Coq.Save.save_vo ~token ~st:state ~ldir ~in_file |> Error.protect_to_result
  in
  Result.iter (fun _ -> Printf.printf "vo saved successfully\n") res;
  res

let transformation_action (doc : Fleche.Doc.t) ~(token : Coq.Limits.Token.t)
    (config : transformation_configuration) =
  let ( let* ) = Result.bind in

  let uri_str = Lang.LUri.File.to_string_uri doc.uri in

  let _ =
    match config.verbosity with
    | Verbose -> Logs.set_level (Some Logs.Debug)
    | Normal | Quiet -> Logs.set_level (Some Logs.Info)
  in

  let _ =
    match config.progress with
    | Some { current_file_count; total_file_count } ->
        Printf.printf
          "Running rocq-ditto on %s (file %d/%d in the project) \n%!" uri_str
          current_file_count total_file_count
    | None -> Printf.printf "running rocq-ditto on %s\n%!" uri_str
  in

  let* parsed_document = Rocq_document.parse_document doc in
  let scoped_transformations : (transformation_kind * scoped_function) list =
    List.map
      (fun x -> (x, transformation_kind_to_scoped_function x))
      config.transformation_steps
  in

  let res =
    List.fold_left
      (fun (doc_acc : (Rocq_document.t, Error.t) result)
           (transformation_kind, transformation) ->
        match (doc_acc, (transformation : scoped_function)) with
        | Ok doc_acc, scoped_trans -> (
            match scoped_trans with
            | ProofScope trans ->
                Printf.printf "applying transformation : %s\n"
                  (transformation_kind_to_string transformation_kind);

                let* proof_list =
                  if config.reverse_order then
                    Result.map List.rev (Rocq_document.get_proofs doc_acc)
                  else Rocq_document.get_proofs doc_acc
                in

                Ok
                  (local_apply_proof_transformation doc_acc trans
                     transformation_kind proof_list config.verbosity)
            | DocScope trans -> local_apply_doc_transformation doc_acc trans)
        | Error err, _ -> Error err)
      (Ok parsed_document) scoped_transformations
  in

  match (res, config.save_vo) with
  | Ok res, false ->
      print_info config.output_filename config.verbosity;
      (* new document repr was computed when applying transformation steps *)
      let doc_repr = res.document_repr in
      Filesystem.write_file config.output_filename doc_repr;
      Ok ()
  | Ok res, true ->
      print_info config.output_filename config.verbosity;
      let* doc_repr = Rocq_document.dump_to_string res in
      Filesystem.write_file config.output_filename doc_repr;
      save_vo_to_file config.output_filename res doc.uri token
  | Error err, _ -> Error err

let ditto_plugin ~io:_ ~(token : Coq.Limits.Token.t) ~(doc : Doc.t) :
    (unit, Error.t) result =
  let ( let* ) = Result.bind in
  let out = Format.std_formatter in
  let reporter =
    Logs_fmt.reporter ~pp_header:pp_header_no_app ~app:out ~dst:out ()
  in
  Logs.set_reporter reporter;

  Printexc.record_backtrace true;

  let diags = List.concat_map (fun (x : Doc.Node.t) -> x.diags) doc.nodes in
  let errors = List.filter Lang.Diagnostic.is_error diags in

  let max_errors = 5 in
  let limited_errors = List.filteri (fun i _ -> i < max_errors) errors in

  match doc.completed with
  | Doc.Completion.Stopped range_stop ->
      Error.format_to_or_error
        "parsing stopped at %s\n\
         %s\n\
         NOTE: errors after the first might be due to the first error."
        (Lang.Range.to_string range_stop)
        (String.concat "\n"
           (List.map Diagnostic_utils.diagnostic_to_string limited_errors))
  | Doc.Completion.Failed range_failed ->
      Error.format_to_or_error
        "parsing failed at %s\n\
         %s\n\
         NOTE: errors after the first might be due to the first error."
        (Lang.Range.to_string range_failed)
        (String.concat "\n"
           (List.map Diagnostic_utils.diagnostic_to_string limited_errors))
  | Doc.Completion.Yes _ -> (
      if errors <> [] then
        Error.format_to_or_error
          "Document was parsed with errors:\n\
           %s\n\
           NOTE: errors after the first might be due to the first error."
          (String.concat "\n"
             (List.map Diagnostic_utils.diagnostic_to_string limited_errors))
      else
        let* plugin_configuration =
          plugin_configuration_of_env (Unix.environment ())
        in

        match plugin_configuration with
        | TransformationAction config -> transformation_action doc ~token config
        | StatisticAction config -> statistic_action doc config)

let ditto_plugin_hook ~io ~token ~(doc : Doc.t) : unit =
  match ditto_plugin ~io ~token ~doc with
  | Ok _ -> exit 0
  | Error err ->
      prerr_endline (Error.to_string_hum err);
      exit 1

let main () = Theory.Register.Completed.add ditto_plugin_hook
let () = main ()
