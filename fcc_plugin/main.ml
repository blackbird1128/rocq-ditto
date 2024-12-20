open Fleche
open Ditto
open Ditto.Proof_tree
open Ditto.Annotated_ast_node
open Vernacexpr

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

let make_from_coq_ast (ast : Coq.Ast.t) (range : Lang.Range.t) :
    annotatedASTNode =
  let node_ast : Doc.Node.Ast.t = { v = ast; ast_info = None } in
  {
    ast = node_ast;
    range;
    id = Unique_id.next ();
    repr = Ppvernac.pr_vernac (Coq.Ast.to_coq ast) |> Pp.string_of_ppcmds;
    proof_id = None;
  }

let depth_to_bullet_type (depth : int) =
  let bullet_number = 1 + (depth / 3) in
  match depth mod 3 with
  | 0 -> VernacBullet (Proof_bullet.Dash bullet_number)
  | 1 -> VernacBullet (Proof_bullet.Plus bullet_number)
  | 2 -> VernacBullet (Proof_bullet.Star bullet_number)
  | _ -> VernacBullet (Proof_bullet.Dash bullet_number)

let create_annotated_ast_bullet (depth : int) (range : Lang.Range.t) =
  let example_without_dirpath : Loc.source =
    InFile { dirpath = None; file = "main.ml" }
  in
  let control_r =
    {
      control = [];
      (* No control flags *)
      attrs = [];
      (* Default attributes *)
      expr =
        VernacSynPure (depth_to_bullet_type depth)
        (* The pure expression we created *);
    }
  in
  let loc = Loc.create example_without_dirpath 0 0 0 0 in
  let vernac_control = CAst.make ~loc control_r in
  let ast_node = Coq.Ast.of_coq vernac_control in
  make_from_coq_ast ast_node range

let push_node_n_char (n_char : int) (node : annotatedASTNode) : annotatedASTNode
    =
  { node with range = Range_transformation.push_range_n_char n_char node.range }

let add_bullet (proof_tree : annotatedASTNode Proof_tree.nary_tree) :
    Ditto.Proof.proof =
  let proof_expr, childrens =
    match proof_tree with Node (e, childrens) -> (e, childrens)
  in
  let rec aux pt depth =
    match pt with
    | Node (e, childs) -> (
        match childs with
        | [] -> [ e ]
        | [ x ] -> e :: aux x depth
        | childrens ->
            List.concat
              (List.map
                 (fun (Node (value, _) as child) ->
                   create_annotated_ast_bullet depth value.range
                   :: push_node_n_char 2 e
                   :: aux child (depth + 1))
                 childrens))
  in
  { proposition = proof_expr; proof_steps = aux (List.hd childrens) 0 }

let dump_ast ~io ~token:_ ~(doc : Doc.t) =
  let uri = doc.uri in
  let uri_str = Lang.LUri.File.to_string_uri uri in
  let document_text = read_whole_file uri_str in
  let lvl = Io.Level.Info in
  Io.Report.msg ~io ~lvl "[ast plugin] dumping ast for %s ..." uri_str;
  let nodes = doc.nodes in

  let parsed_document =
    Coq_document.parse_document nodes document_text uri_str
  in
  let modified = Coq_document.remove_node_with_id 3 parsed_document in
  print_endline (Coq_document.dump_to_string modified);
  print_endline "---------------------------";

  let out = open_out (Filename.remove_extension uri_str ^ "_bis.v") in
  output_string out (Coq_document.dump_to_string modified);

  ()
(* let first_tree = List.hd trees in *)
(* let first_proof_with_bullets = add_bullet first_tree in *)

(* let updated = *)
(*   Coq_document.replace_coq_element (CoqStatement first_proof_with_bullets) *)
(*     parsed_document *)
(* in *)

(* let annotated_nodes = *)
(*   List.concat_map *)
(*     (fun elem -> *)
(*       match elem with *)
(*       | Coq_document.CoqNode e -> [ e ] *)
(*       | Coq_document.CoqStatement p -> Proof.proof_nodes p) *)
(*     parsed_document.elements *)
(* in *)

(* let asts = *)
(*   List.map *)
(*     (fun (node : Annotated_ast_node.annotatedASTNode) -> node.ast) *)
(*     annotated_nodes *)
(* in *)
(* let out_file_j = Lang.LUri.File.to_string_file uri ^ ".astdump.json" in *)
(* let out_chan = open_out out_file_j in *)
(* Yojson.Safe.pretty_to_channel out_chan *)
(*   (`List *)
(*     (List.map (fun (x : Doc.Node.Ast.t) -> Lsp.JCoq.Ast.to_yojson x.v) asts)); *)
(* () *)

let main () = Theory.Register.Completed.add dump_ast
let () = main ()
