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

  let modifed_doc =
    List.fold_left
      (fun doc_acc proof ->
        let new_proof_res =
          Transformations.fold_replace_assumption_with_apply doc proof
        in
        match new_proof_res with
        | Ok new_proof -> (
            match Coq_document.replace_proof new_proof doc_acc with
            | Ok new_doc -> new_doc
            | Error _ -> doc_acc)
        | Error _ -> doc_acc)
      parsed_document proof_trees
  in

  let out = open_out (Filename.remove_extension uri_str ^ "_bis.v") in
  output_string out (Coq_document.dump_to_string modifed_doc)

let main () = Theory.Register.Completed.add dump_ast
let () = main ()
