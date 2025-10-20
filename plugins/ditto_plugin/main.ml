open Fleche
open Ditto
open Ditto.Proof
open Ditto.Diagnostic_utils

type transformation_kind =
  | Help
  | ExplicitFreshVariables
  | TurnIntoOneliner
  | ReplaceAutoWithSteps
  | CompressIntro
  | IdTransformation
[@@deriving variants]

let camel_to_snake (s : string) : string =
  let b = Buffer.create (String.length s * 2) in
  String.iteri
    (fun i c ->
      if 'A' <= c && c <= 'Z' then (
        if i > 0 then Buffer.add_char b '_';
        Buffer.add_char b (Char.lowercase_ascii c))
      else Buffer.add_char b c)
    s;
  Buffer.contents b

let transformation_kind_to_string (kind : transformation_kind) : string =
  Variants_of_transformation_kind.to_name kind |> camel_to_snake

let arg_to_transformation_kind (arg : string) :
    (transformation_kind, Error.t) result =
  let normalized = String.lowercase_ascii arg in
  if normalized = "help" then Ok Help
  else if normalized = "explicit_fresh_variables" then Ok ExplicitFreshVariables
  else if normalized = "turn_into_oneliner" then Ok TurnIntoOneliner
  else if normalized = "replace_auto_with_steps" then Ok ReplaceAutoWithSteps
  else if normalized = "compress_intro" then Ok CompressIntro
  else if normalized = "id_transformation" then Ok IdTransformation
  else
    Error.string_to_or_error_err
      ("transformation " ^ arg ^ " wasn't recognized as a valid transformation")

let wrap_to_treeify (doc : Coq_document.t) (x : proof) =
  Result.get_ok (Runner.treeify_proof doc x)

let transformation_kind_to_function (kind : transformation_kind) :
    Coq_document.t -> Proof.proof -> (transformation_step list, Error.t) result
    =
  match kind with
  | Help -> fun _ _ -> Ok []
  | ExplicitFreshVariables -> Transformations.explicit_fresh_variables
  | TurnIntoOneliner ->
      fun doc x ->
        Transformations.turn_into_oneliner doc (wrap_to_treeify doc x)
  | ReplaceAutoWithSteps -> Transformations.replace_auto_with_steps
  | CompressIntro -> Transformations.compress_intro
  | IdTransformation -> Transformations.id_transform

let print_help (transformation_help : (transformation_kind * string) list) :
    unit =
  List.iter
    (fun (kind, help) ->
      print_endline (transformation_kind_to_string kind ^ ": " ^ help);
      print_newline ())
    transformation_help

let transformations_help =
  [
    ( ExplicitFreshVariables,
      "replace call to tactics creating fresh variables such as intros with \
       intros V_1  V_2 V_n\n\
       where each V_i corresponds to a variable automatically introduced by \
       the tactic." );
    ( TurnIntoOneliner,
      "Remove all commands from the proof and turn all steps into a single \
       tactic call using the ';' and '[]' tacticals." );
    ( ReplaceAutoWithSteps,
      "Replace all calls to the 'auto' tactic with the steps effectively used \
       by auto using 'info_auto' trace." );
    ( CompressIntro,
      "Replace consecutive calls to the 'intro' tactic with one call to \
       'intros'." );
    (IdTransformation, "Keep the file the same.");
  ]

let local_apply_proof_transformation (doc_acc : Coq_document.t)
    (transformation :
      Coq_document.t -> proof -> (transformation_step list, Error.t) result)
    (transformation_kind : transformation_kind)
    (proofs_rec : (proof list, Error.t) result) (verbose : bool) =
  match proofs_rec with
  | Ok proofs ->
      let proof_total = List.length proofs in
      List.fold_left
        (fun ((doc_acc_bis, proof_count) :
               (Coq_document.t, Error.t) result * int) (proof : Proof.proof) ->
          match doc_acc_bis with
          | Ok acc -> (
              let proof_name =
                Option.default "anonymous" (Proof.get_proof_name proof)
              in
              let _ =
                if verbose then (
                  Printf.printf "Running transformation %s on %-20s(%d/%d)%!\n"
                    (transformation_kind_to_string transformation_kind)
                    proof_name (proof_count + 1) proof_total;
                  print_newline ())
                else
                  Printf.printf
                    "\027[2K\rRunning transformation %s on %-20s(%d/%d)%!"
                    (transformation_kind_to_string transformation_kind)
                    proof_name (proof_count + 1) proof_total
              in

              let transformation_steps = transformation acc proof in
              match transformation_steps with
              | Ok steps ->
                  ( List.fold_left
                      (fun doc_acc_err step ->
                        match doc_acc_err with
                        | Ok doc ->
                            Coq_document.apply_transformation_step step doc
                        | Error err -> Error err)
                      doc_acc_bis steps,
                    proof_count + 1 )
              | Error err -> (Error err, proof_count))
          | Error err -> (Error err, proof_count))
        (Ok doc_acc, 0) proofs
  | Error err -> (Error err, 0)

let dump_ast ~io:_ ~token:_ ~(doc : Doc.t) =
  let verbose = Option.default "false" (Sys.getenv_opt "DEBUG_LEVEL") in

  let verbose = Option.default false (bool_of_string_opt verbose) in

  Logs.set_reporter (Logs_fmt.reporter ());

  if verbose then Logs.set_level (Some Logs.Debug)
  else Logs.set_level (Some Logs.Info);

  Printexc.record_backtrace true;
  let uri = doc.uri in
  let uri_str = Lang.LUri.File.to_string_uri uri in
  let diags = List.concat_map (fun (x : Doc.Node.t) -> x.diags) doc.nodes in
  let errors = List.filter Lang.Diagnostic.is_error diags in

  let max_errors = 5 in

  match doc.completed with
  | Doc.Completion.Stopped range_stop ->
      prerr_endline ("parsing stopped at " ^ Lang.Range.to_string range_stop);
      print_diagnostics (List.filteri (fun i _ -> i < max_errors) errors);
      print_endline
        "NOTE: errors after the first might be due to the first error."
  | Doc.Completion.Failed range_failed ->
      prerr_endline ("parsing failed at " ^ Lang.Range.to_string range_failed);
      print_diagnostics (List.filteri (fun i _ -> i < max_errors) errors);
      print_endline
        "NOTE: errors after the first might be due to the first error."
  | Doc.Completion.Yes _ -> (
      if errors <> [] then (
        let first_errors = List.filteri (fun i _ -> i < 5) errors in
        print_diagnostics first_errors;
        print_endline
          "NOTE: errors after the first might be due to the first error.")
      else
        let transformations_steps =
          Sys.getenv_opt "DITTO_TRANSFORMATION"
          |> Option.map (String.split_on_char ',')
          |> Option.map (List.map arg_to_transformation_kind)
        in

        match transformations_steps with
        | None ->
            prerr_endline
              "Please specify the wanted transformation using the environment \
               variable: DITTO_TRANSFORMATION";
            prerr_endline
              "If you want help about the different transformation, specify \
               DITTO_TRANSFORMATION=HELP";
            exit 1
        | Some steps when List.exists Result.is_error steps ->
            prerr_endline "Transformations not recognized:";
            List.iter
              (fun x ->
                print_endline (Error.to_string_hum (Result.get_error x)))
              ((List.filter Result.is_error) steps);
            print_endline "Recognized transformations: ";
            let transformations =
              let add acc var = var.Variantslib.Variant.name :: acc in
              Variants_of_transformation_kind.fold ~init:[] ~help:add
                ~explicitfreshvariables:add ~turnintooneliner:add
                ~compressintro:add ~idtransformation:add
                ~replaceautowithsteps:add
              |> List.map camel_to_snake
            in

            List.iter print_endline transformations
        | Some steps when List.mem (Ok Help) steps ->
            print_help transformations_help
        | Some steps -> (
            let transformations_steps = List.map Result.get_ok steps in
            let parsed_document = Coq_document.parse_document doc in
            let transformations =
              List.map
                (fun x -> (x, transformation_kind_to_function x))
                transformations_steps
            in

            let res =
              List.fold_left
                (fun (doc_acc : (Coq_document.t, Error.t) result)
                     (transformation_kind, transformation) ->
                  match doc_acc with
                  | Ok doc_acc -> (
                      print_endline
                        ("applying transformation : "
                        ^ transformation_kind_to_string transformation_kind);
                      let proofs_rec = Coq_document.get_proofs doc_acc in
                      let doc_res =
                        local_apply_proof_transformation doc_acc transformation
                          transformation_kind proofs_rec verbose
                      in
                      match doc_res with
                      | Ok new_doc, _ -> Ok new_doc
                      | Error err, _ -> Error err)
                  | Error err -> Error err)
                (Ok parsed_document) transformations
            in

            let filename =
              Option.default
                (Filename.remove_extension uri_str ^ "_bis.v")
                (Sys.getenv_opt "OUTPUT_FILENAME")
            in
            match res with
            | Ok res ->
                print_newline ();
                print_endline
                  ("All transformations applied, writing to file " ^ filename);

                let out = open_out filename in
                Result.fold ~ok:(output_string out)
                  ~error:(fun e -> print_endline (Error.to_string_hum e))
                  (Coq_document.dump_to_string res)
            | Error err ->
                print_endline (Error.to_string_hum err);
                exit 1))

let main () = Theory.Register.Completed.add dump_ast
let () = main ()
