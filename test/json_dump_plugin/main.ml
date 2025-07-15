open Fleche
open Ditto
open Ditto.Nary_tree
open Ditto.Proof
open Ditto.Syntax_node
open Vernacexpr

let dump_ast ~io ~token:_ ~(doc : Doc.t) =
  let uri = doc.uri in
  let uri_str = Lang.LUri.File.to_string_uri uri in
  let lvl = Io.Level.Info in
  Io.Report.msg ~io ~lvl "[json dump plugin] dumping ast for %s ..." uri_str;

  let parsed_asts =
    List.filter_map (fun (node : Doc.Node.t) -> node.ast) doc.nodes
  in
  let parsed_asts_json =
    List.map
      (fun (ast : Doc.Node.Ast.t) -> Lsp.JCoq.Ast.to_yojson ast.v)
      parsed_asts
  in

  let out_file_j = Lang.LUri.File.to_string_file uri ^ ".jsondump.json" in
  let out_chan = open_out out_file_j in

  Yojson.Safe.pretty_to_channel out_chan (`List parsed_asts_json)

let main () = Theory.Register.Completed.add dump_ast
let () = main ()
