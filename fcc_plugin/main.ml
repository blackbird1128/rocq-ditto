open Fleche
open Ditto
open Ditto.Proof_tree
open Ditto.Proof
open Ditto.Syntax_node
open Vernacexpr

let dump_ast ~io ~token:_ ~(doc : Doc.t) =
  let uri = doc.uri in
  let uri_str = Lang.LUri.File.to_string_uri uri in
  match doc.completed with
  | Doc.Completion.Yes _ ->
      let parsed_document = Coq_document.parse_document doc in

      let proofs = Coq_document.get_proofs parsed_document in

      let proof_trees =
        List.filter_map
          (fun proof ->
            Result.to_option (Runner.treeify_proof parsed_document proof))
          proofs
      in

      print_endline ("number of proofs : " ^ string_of_int (List.length proofs));

      let diags = List.concat_map (fun (x : Doc.Node.t) -> x.diags) doc.nodes in

      List.iter
        (fun (diag : Lang.Diagnostic.t) ->
          prerr_endline
            (Transformations.error_location_to_string diag.range
            ^ " "
            ^ Pp.string_of_ppcmds diag.message))
        diags;

      let modified_doc =
        List.fold_left
          (fun doc_acc proof ->
            let transformation_steps =
              Transformations.replace_auto_with_info_auto doc_acc proof
            in

            match transformation_steps with
            | Ok steps -> (
                let doc_with_steps_applied =
                  List.fold_left
                    (fun doc_acc_err step ->
                      match doc_acc_err with
                      | Ok doc ->
                          Coq_document.apply_transformation_step step doc
                      | Error err -> Error err)
                    (Ok doc_acc) steps
                in
                match doc_with_steps_applied with
                | Ok new_doc -> new_doc
                | Error err -> doc_acc)
            | Error err -> doc_acc)
          parsed_document proofs
      in
      let out = open_out (Filename.remove_extension uri_str ^ "_bis.v") in
      output_string out (Coq_document.dump_to_string modified_doc);
      ()
  | Doc.Completion.Stopped range ->
      print_endline ("parsing stopped at : " ^ Lang.Range.to_string range);
      ()
  | Doc.Completion.Failed range ->
      print_endline ("parsing of " ^ uri_str ^ " failed");
      print_endline "parsing failed at : ";
      flush stderr;
      let diags = List.concat_map (fun (x : Doc.Node.t) -> x.diags) doc.nodes in
      let first_errors = List.filteri (fun i a -> i < 3) diags in

      List.iter
        (fun (diag : Lang.Diagnostic.t) ->
          prerr_endline
            (Transformations.error_location_to_string diag.range
            ^ " "
            ^ Pp.string_of_ppcmds diag.message))
        first_errors;

      ()

let main () = Theory.Register.Completed.add dump_ast
let () = main ()
