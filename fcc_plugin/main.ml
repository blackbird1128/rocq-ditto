open Fleche
open Ditto
open Ditto.Proof_tree
open Ditto.Proof
open Ditto.Annotated_ast_node
open Vernacexpr

let dump_ast ~io ~token:_ ~(doc : Doc.t) =
  let uri = doc.uri in
  let uri_str = Lang.LUri.File.to_string_uri uri in
  let document_text = doc.contents.raw in
  let lvl = Io.Level.Info in
  Io.Report.msg ~io ~lvl "[ast plugin] dumping ast for %s ..." uri_str;
  let nodes = doc.nodes in
  let parsed_document =
    Coq_document.parse_document nodes document_text uri_str
  in

  let proofs = Coq_document.get_proofs parsed_document in

  let proof_trees = List.map (Proof.treeify_proof doc) proofs in

  let first_proof_tree = List.nth proof_trees 0 in
  print_tree first_proof_tree " ";

  let new_proof_err =
    Transformations.fold_replace_assumption_with_apply doc first_proof_tree
  in
  match new_proof_err with
  | Ok new_proof -> (
      (* let bulleted = Result.get_ok (fold_replace_by_lia doc first_proof_tree) in *)
      let modified = Coq_document.replace_proof new_proof parsed_document in

      match modified with
      | Ok res ->
          let out = open_out (Filename.remove_extension uri_str ^ "_bis.v") in
          output_string out (Coq_document.dump_to_string res)
      | Error msg ->
          print_endline "error";
          print_endline msg)
  | Error err -> print_endline "err"

let main () = Theory.Register.Completed.add dump_ast
let () = main ()
