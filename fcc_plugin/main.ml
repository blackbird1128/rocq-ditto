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

let rec proof_tree_to_minimized_proof (proof_tree : string nary_tree) =
  match proof_tree with
  | Node (tactic, childrens) -> (
      match childrens with
      | [] -> tactic
      | [ next ] -> tactic ^ ";" ^ proof_tree_to_minimized_proof next
      | childs ->
          let child_length = List.length childs in
          tactic ^ ";"
          ^ fst
              (List.fold_left
                 (fun (acc, idx) child ->
                   if idx < child_length - 1 then
                     (acc ^ proof_tree_to_minimized_proof child ^ "|", idx + 1)
                   else
                     (acc ^ proof_tree_to_minimized_proof child ^ "]", idx + 1))
                 ("[", 0) childs))

let read_whole_file filename =
  (* open_in_bin works correctly on Unix and Windows *)
  let ch = open_in_bin filename in
  let s = really_input_string ch (in_channel_length ch) in
  close_in ch;
  s

let dump_ast ~io ~token:_ ~(doc : Doc.t) =
  let uri = doc.uri in
  let uri_str = Lang.LUri.File.to_string_uri uri in
  let document_text = read_whole_file uri_str in
  (* print_endline document_text; *)
  let lvl = Io.Level.Info in
  Io.Report.msg ~io ~lvl "[ast plugin] dumping ast for %s ..." uri_str;
  let nodes = doc.nodes in
  let nodes_with_ast =
    List.filter (fun elem -> Option.has_some (Doc.Node.ast elem)) nodes
  in

  List.iter
    (fun n -> print_endline (Lang.Range.to_string (Doc.Node.range n)))
    nodes_with_ast;

  let parsed_document = Coq_document.parse_document nodes document_text in
  let out = open_out (Filename.remove_extension uri_str ^ "_bis.v") in
  output_string out (Coq_document.dump_to_string parsed_document);

  (* List.iter
     (fun element ->
       match element with
       | CoqNode e -> print_endline (doc_node_to_string e)
       | CoqStatement p -> print_endline (Proof.proof_to_coq_script_string p))
     parsed_document; *)
  let proofs = Coq_document.get_proofs parsed_document in

  (* List.iter *)
  (*   (fun proof -> *)
  (*     print_endline (proof_tree_to_minimized_proof (treeify_proof proof doc))) *)
  (*   proofs; *)

  (* let out_file_j = Lang.LUri.File.to_string_file uri ^ ".astdump.json" in *)
  (* let proofs = Coq_document.get_proofs parsed_document in *)

  (* let proof_propositions = List.map (fun proof -> proof.proposition) proofs in
     List.iter
       (fun (prop : Doc.Node.Ast.t) -> print_endline (doc_node_to_string prop))
       proof_propositions;

     let ast_infos_options =
       List.map (fun (prop : Doc.Node.Ast.t) -> prop.ast_info) proof_propositions
     in
     List.iter
       (fun info_opt ->
         let infos = Option.get info_opt in
         List.iter
           (fun (info : Lang.Ast.Info.t) ->
             print_endline (Lang.Range.to_string info.range))
           infos)
       ast_infos_options;
     let out_chan = open_out out_file_j in
     Yojson.Safe.pretty_to_channel out_chan
       (`List
         (List.map (fun (x : Doc.Node.Ast.t) -> Lsp.JCoq.Ast.to_yojson x.v) asts)); *)
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
