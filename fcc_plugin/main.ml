open Fleche
open Ditto
open Ditto.Proof_tree
open Ditto.Proof
open Ditto.Syntax_node
open Vernacexpr

let error_location_to_string (location : Lang.Range.t) =
  if location.start.line = location.end_.line then
    "line "
    ^ string_of_int location.start.line
    ^ ", characters: "
    ^ string_of_int location.start.character
    ^ "-"
    ^ string_of_int location.end_.character
  else
    "line "
    ^ string_of_int location.start.line
    ^ "-"
    ^ string_of_int location.end_.line
    ^ ", characters: "
    ^ string_of_int location.start.character
    ^ "-"
    ^ string_of_int location.end_.character

let dump_ast ~io ~token:_ ~(doc : Doc.t) =
  let uri = doc.uri in
  let uri_str = Lang.LUri.File.to_string_uri uri in
  match doc.completed with
  | Doc.Completion.Yes _ ->
      let nodes = doc.nodes in

      let document_text = doc.contents.raw in

      let parsed_document =
        Coq_document.parse_document nodes document_text uri_str
      in

      let proofs = Coq_document.get_proofs parsed_document in
      (* let first_proof : Proof.proof = List.hd proofs in *)
      (* let expr = first_proof.proposition in *)
      (* let expr_ast = Option.get expr.ast in *)
      (* let coq_ast = Coq.Ast.to_coq expr_ast.v in *)
      (* let x = *)
      (*   match coq_ast.CAst.v.expr with *)
      (*   | VernacSynterp _ -> false *)
      (*   | VernacSynPure expr -> ( *)
      (*       match expr with *)
      (*       | Vernacexpr.VernacStartTheoremProof (theorem_kind, expr_list) -> *)
      (*           List.iter *)
      (*             (fun (expr : proof_expr) -> *)
      (*               let ident_dcl, t_data = expr in *)
      (*               let ident_name, univ = ident_dcl in *)
      (*               Format.printf "loc: %s\n" *)
      (*                 (Option.default "not found" *)
      (*                    (Option.map Coq.Ast.loc_to_string ident_name.loc))) *)
      (*             expr_list; *)
      (*           true *)
      (*       | _ -> false) *)
      (* in *)

      print_endline ("number of proofs : " ^ string_of_int (List.length proofs));

      let diags = List.concat_map (fun (x : Doc.Node.t) -> x.diags) doc.nodes in

      List.iter
        (fun (diag : Lang.Diagnostic.t) ->
          prerr_endline
            (error_location_to_string diag.range
            ^ " "
            ^ Pp.string_of_ppcmds diag.message))
        diags;

      let proof_trees =
        List.filter_map
          (fun proof -> Result.to_option (Proof.treeify_proof doc proof))
          proofs
      in

      let modified_doc =
        List.fold_left
          (fun doc_acc proof ->
            let transformation_steps =
              Transformations.make_intros_explicit doc proof
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
      print_endline Fleche.Version.server;
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
            (error_location_to_string diag.range
            ^ " "
            ^ Pp.string_of_ppcmds diag.message))
        first_errors;

      ()

let main () = Theory.Register.Completed.add dump_ast
let () = main ()
