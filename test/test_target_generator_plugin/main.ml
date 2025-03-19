open Fleche
open Ditto
open Ditto.Proof_tree
open Ditto.Proof
open Ditto.Syntax_node
open Vernacexpr

let dump_ast ~io ~token:_ ~(doc : Doc.t) =
  let uri = doc.uri in
  let uri_str = Lang.LUri.File.to_string_uri uri in
  let document_text = doc.contents.raw in
  let lvl = Io.Level.Info in
  Io.Report.msg ~io ~lvl "[ast plugin] dumping ast for %s ..." uri_str;
  let nodes = doc.nodes in

  let parsed_document =
    Coq_document.parse_document doc 
  in

  let repr_and_ranges =
    List.map
      (fun node ->
        `Assoc
          [ ("repr", `String node.repr); ("range", range_to_yojson node.range) ])
      parsed_document.elements
  in
  let json_repr = `List repr_and_ranges in

  let out_file_j = Lang.LUri.File.to_string_file uri ^ ".target.json" in
  let out_chan = open_out out_file_j in

  Yojson.Safe.pretty_to_channel out_chan json_repr

let main () = Theory.Register.Completed.add dump_ast
let () = main ()
