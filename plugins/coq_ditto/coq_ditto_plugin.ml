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
      List.fold_left
        (fun (acc : ('a, Error.t) result) (x : Proof.t) ->
          match acc with
          | Ok acc -> (
              let compute_res = compute doc x in
              match compute_res with
              | Ok value -> Ok (statistic.combine acc value)
              | Error err -> Error err)
          | Error _ -> acc)
        (Ok statistic.empty) proofs
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
    (Syntax_node.t Nary_tree.nary_tree, Error.t) result =
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
    (trans : Rocq_document.t -> (Transforming_step.t list, Error.t) result)
    (_transformation_kind : transformation_kind) (_verbose : bool)
    (_quiet : bool) : (Rocq_document.t, Error.t) result =
  Transformations.apply_doc_transformation trans doc_acc

let print_current_running (proof_count : int) (proof_total : int)
    (proof_name : string) (transformation_kind : transformation_kind) quiet
    verbose =
  if verbose then
    Printf.printf "Running transformation %s on %-20s (%d/%d)%!\n%!"
      (transformation_kind_to_string transformation_kind)
      proof_name (proof_count + 1) proof_total
  else if not quiet then
    Printf.printf "\027[2K\rRunning transformation %s on %-20s(%d/%d)%!"
      (transformation_kind_to_string transformation_kind)
      proof_name (proof_count + 1) proof_total
  else ()

let apply_steps
    (transformation_steps : (Transforming_step.t list, Error.t) result)
    (curr_doc : Rocq_document.t) (proof_count : int) (proof : 'a) =
  match transformation_steps with
  | Ok steps ->
      ( List.fold_left
          (fun doc_acc_err step ->
            match doc_acc_err with
            | Ok doc -> Rocq_document.apply_transformation_step step doc
            | Error err -> Error err)
          (Ok curr_doc) steps,
        proof_count + 1,
        curr_doc,
        Some proof )
  | Error err -> (Error err, proof_count, curr_doc, Some proof)

let display_transformation_error (prev_proof : Proof.t option)
    (transformation_kind : transformation_kind) (err : Error.t) =
  let prev_proof_name =
    match prev_proof with
    | Some prev_proof ->
        Option.default "anonymous" (Proof.get_proof_name prev_proof)
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
    (verbose : bool) (quiet : bool) : Rocq_document.t =
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
          Runner.get_init_state curr_doc proof.proposition token
        in
        let proof_name =
          Option.default "anonymous" (Proof.get_proof_name proof)
        in
        print_current_running proof_count proof_total proof_name
          transformation_kind quiet verbose;
        match status_before with
        | Ok _ ->
            let transformation_steps = transformation curr_doc proof in
            apply_steps transformation_steps curr_doc proof_count proof
        | Error _ ->
            let prev_proof_name =
              Option.map (fun p -> Proof.get_proof_name p) prev_proof
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

let print_info (filename : string) (verbose : bool) : unit =
  Printf.printf "\nAll transformations applied, writing to file %s\n%!" filename;

  if verbose then (
    let stats = Stats.Global.dump () in
    Printf.printf "rocq-ditto stats: %s\n" (Stats.Global.to_string stats);
    Printf.printf "rocq-ditto %s\n" (Memo.GlobalCacheStats.stats ()))
  else ()

let statistic_action (doc : Fleche.Doc.t) =
  let ( let* ) = Result.bind in
  let statistic_kind_opt =
    Sys.getenv_opt "DITTO_STATISTIC" |> Option.map arg_to_statistic_kind
  in

  let* output_format =
    Sys.getenv_opt "DITTO_STAT_FORMAT"
    |> Option.default "text" |> arg_to_output_format
  in

  match statistic_kind_opt with
  | None ->
      Error.string_to_or_error
        "Please specify the statistic wanted using the environement variable: \
         DITTO_STATISTIC"
  | Some (Error err) ->
      let not_recognized = Error.to_string_hum err in

      Error.format_to_or_error
        "Statistic not recognized:\n%s\nRecognized statistics: %s "
        not_recognized
        (String.concat "\n" statistics_list)
  | Some (Ok statistic_kind) ->
      let* parsed_doc = Rocq_document.parse_document doc in

      if output_format = Text then
        Printf.printf "applying statistic : %s\n"
          (statistic_kind_to_string statistic_kind);

      let statistic = statistic_kind_to_statistic statistic_kind in
      let* value = run_statistic parsed_doc statistic in
      (match output_format with
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

let write_file (filename : string) (contents : string) =
  let out = open_out filename in
  Fun.protect
    ~finally:(fun () -> close_out_noerr out)
    (fun () ->
      output_string out contents;
      flush out)

let transformation_action (doc : Fleche.Doc.t) ~(token : Coq.Limits.Token.t) =
  let ( let* ) = Result.bind in

  let uri_str = Lang.LUri.File.to_string_uri doc.uri in

  let total_files =
    Sys.getenv_opt "TOTAL_FILE_COUNT"
    |> Option.map int_of_string_opt
    |> Option.flatten
  in

  let current_file_count =
    Sys.getenv_opt "CURRENT_FILE_COUNT"
    |> Option.map int_of_string_opt
    |> Option.flatten
  in

  let verbose = Option.default "false" (Sys.getenv_opt "DEBUG_LEVEL") in
  let verbose = Option.default false (bool_of_string_opt verbose) in

  if verbose then Logs.set_level (Some Logs.Debug)
  else Logs.set_level (Some Logs.Info);

  let quiet =
    Option.default "false" (Sys.getenv_opt "QUIET")
    |> bool_of_string_opt |> Option.default false
  in

  let _ =
    match (current_file_count, total_files) with
    | Some curr_count, Some total_files ->
        Printf.printf
          "Running rocq-ditto on %s (file %d/%d in the project) \n%!" uri_str
          curr_count total_files
    | _, _ -> Printf.printf "running rocq-ditto on %s\n%!" uri_str
  in

  let transformations_steps =
    Sys.getenv_opt "DITTO_TRANSFORMATION"
    |> Option.map (String.split_on_char ',')
    |> Option.map (List.map arg_to_transformation_kind)
  in

  let reverse_order =
    Option.default false
      (Sys.getenv_opt "REVERSE_ORDER"
      |> Option.map bool_of_string_opt
      |> Option.flatten)
  in

  match transformations_steps with
  | None ->
      Error.string_to_or_error
        "Please specify the wanted transformation using the environment \
         variable: DITTO_TRANSFORMATION\n"
  | Some steps when List.exists Result.is_error steps ->
      let not_recognized =
        String.concat "\n"
          (List.map
             (fun x -> Error.to_string_hum (Result.get_error x))
             ((List.filter Result.is_error) steps))
      in
      Error.format_to_or_error
        "Transformations not recognized:\n%s\nRecognized transformations: %s"
        not_recognized
        (String.concat "\n" transformations_list)
  | Some steps -> (
      let transformations_steps = List.map Result.get_ok steps in
      let* parsed_document = Rocq_document.parse_document doc in
      let scoped_transformations : (transformation_kind * scoped_function) list
          =
        List.map
          (fun x -> (x, transformation_kind_to_scoped_function x))
          transformations_steps
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
                      if reverse_order then
                        Result.map List.rev (Rocq_document.get_proofs doc_acc)
                      else Rocq_document.get_proofs doc_acc
                    in

                    Ok
                      (local_apply_proof_transformation doc_acc trans
                         transformation_kind proof_list verbose quiet)
                | DocScope trans ->
                    local_apply_doc_transformation doc_acc trans
                      transformation_kind verbose quiet)
            | Error err, _ -> Error err)
          (Ok parsed_document) scoped_transformations
      in

      let filename =
        Option.default
          (Filename.remove_extension uri_str ^ "_bis.v")
          (Sys.getenv_opt "OUTPUT_FILENAME")
      in

      let save_vo =
        Option.default false
          (Sys.getenv_opt "SAVE_VO"
          |> Option.map bool_of_string_opt
          |> Option.flatten)
      in

      match (res, save_vo) with
      | Ok res, false ->
          print_info filename verbose;
          (* new document repr was computed when applying transformation steps *)
          let doc_repr = res.document_repr in
          write_file filename doc_repr;
          Ok ()
      | Ok res, true ->
          print_info filename verbose;
          let* doc_repr = Rocq_document.dump_to_string res in
          write_file filename doc_repr;
          save_vo_to_file filename res doc.uri token
      | Error err, _ -> Error err)

let ditto_plugin ~io:_ ~(token : Coq.Limits.Token.t) ~(doc : Doc.t) :
    (unit, Error.t) result =
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
        let action = Sys.getenv_opt "DITTO_ACTION" in

        match action with
        | Some "transform" -> transformation_action doc ~token
        | Some "statistics" -> statistic_action doc
        | Some other_action ->
            Error.format_to_or_error "Unknown action %s" other_action
        | None -> Error.string_to_or_error "Please provide an action")

let ditto_plugin_hook ~io ~token ~(doc : Doc.t) : unit =
  match ditto_plugin ~io ~token ~doc with
  | Ok _ -> exit 0
  | Error err ->
      prerr_endline (Error.to_string_hum err);
      exit 1

let main () = Theory.Register.Completed.add ditto_plugin_hook
let () = main ()
