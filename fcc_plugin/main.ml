open Fleche
open Ditto
open Ditto.Proof_tree
open Ditto.Proof
open Ditto.Syntax_node
open Vernacexpr

let print_lident (x : Names.lident) = print_endline (Names.Id.to_string x.v)

let dump_ast ~io ~token:_ ~(doc : Doc.t) =
  let uri = doc.uri in
  let uri_str = Lang.LUri.File.to_string_uri uri in
  match doc.completed with
  | Doc.Completion.Yes _ ->
      let parsed_document = Coq_document.parse_document doc in

      let proofs = Result.get_ok (Coq_document.get_proofs parsed_document) in

      (* let first_proof = List.hd proofs in *)
      (* let statement = first_proof.proposition in *)
      (* let statement_ast = Option.get statement.ast in *)

      (* let _ = *)
      (*   match (Coq.Ast.to_coq statement_ast.v).CAst.v.expr with *)
      (*   | VernacSynterp _ -> *)
      (*       print_endline "BBB"; *)
      (*       false *)
      (*   | VernacSynPure expr -> ( *)
      (*       match expr with *)
      (*       | Vernacexpr.VernacStartTheoremProof *)
      (*           (kind, [ ((ident, univ), (args, expr)) ]) -> *)
      (*           print_endline "AAAA"; *)
      (*           print_lident ident; *)
      (*           true *)
      (*       | _ -> false) *)
      (* in *)
      (* print_endline statement.repr; *)
      let proof_trees =
        List.filter_map
          (fun proof ->
            Result.to_option (Runner.treeify_proof parsed_document proof))
          proofs
      in

      List.iter (fun tree -> Proof.print_tree tree " ") proof_trees;

      print_endline ("number of proofs : " ^ string_of_int (List.length proofs));

      (* let diags = List.concat_map (fun (x : Doc.Node.t) -> x.diags) doc.nodes in

      List.iter
        (fun (diag : Lang.Diagnostic.t) ->
          prerr_endline
            (Transformations.error_location_to_string diag.range
            ^ " "
            ^ Pp.string_of_ppcmds diag.message))
        diags; *)
      let transformations = [ Transformations.turn_into_oneliner ] in

      let res =
        List.fold_left
          (fun (doc_acc : Coq_document.t) transformation ->
            let doc_res =
              Transformations.apply_proof_tree_transformation transformation
                doc_acc
            in
            match doc_res with Ok new_doc -> new_doc | Error err -> doc_acc)
          parsed_document transformations
      in
      List.iter (fun node -> print_endline node.repr) res.elements;

      let out = open_out (Filename.remove_extension uri_str ^ "_bis.v") in
      output_string out (Coq_document.dump_to_string res);
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
