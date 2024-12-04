open Fleche
open Ditto
open Ditto.Proof
(* open Stack  *)

let parse_json_list json_repr =
  match json_repr with
  | `List elements -> elements
  | _ -> failwith "Expected a JSON list"

let rec depth_first_print (Node (value, children)) =
  (* Print the current node's value *)
  print_endline value;
  (* Change this to match your type *)
  (* Recursively traverse each child *)
  List.iter depth_first_print children

let dump_ast ~io ~token:_ ~(doc : Doc.t) =
  let uri = doc.uri in
  let uri_str = Lang.LUri.File.to_string_uri uri in
  let lvl = Io.Level.Info in
  Io.Report.msg ~io ~lvl "[ast plugin] dumping ast for %s ..." uri_str;
  let asts = Doc.asts doc in
  let parsed_document = Coq_document.parse_document asts in

  let out_file_j = Lang.LUri.File.to_string_file uri ^ ".astdump.json" in
  let proofs = Coq_document.get_proofs parsed_document in

  let out_chan = open_out out_file_j in
  Yojson.Safe.pretty_to_channel out_chan
    (`List
      (List.map (fun (x : Doc.Node.Ast.t) -> Lsp.JCoq.Ast.to_yojson x.v) asts));

  List.iter
    (fun proof ->
      Proof.print_tree (treeify_proof proof doc) " ";
      print_newline ())
    proofs;

  (* List.iter
    (fun proof ->
      depth_first_print (treeify_proof proof doc);
      print_newline ())
    proofs; *)
  ()

let main () = Theory.Register.Completed.add dump_ast
let () = main ()
