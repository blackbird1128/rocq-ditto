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

  let out_file_j = Lang.LUri.File.to_string_file uri ^ ".astdump.json" in
  let out_chan = open_out out_file_j in
  Yojson.Safe.pretty_to_channel out_chan
    (Coq_document.doc_to_yojson parsed_document)

let main () = Theory.Register.Completed.add dump_ast
let () = main ()
