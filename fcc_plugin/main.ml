open Fleche
open Ditto
open Ditto.Proof_tree
open Ditto.Proof
open Ditto.Annotated_ast_node
open Vernacexpr

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

let create_annotated_ast_bullet (depth : int) (range : Lang.Range.t) :
    annotatedASTNode =
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

let add_bullets (proof_tree : annotatedASTNode nary_tree) : Ditto.Proof.proof =
  let rec aux (depth : int) (node : annotatedASTNode nary_tree) =
    match node with
    | Node (x, []) -> [ x ]
    | Node (x, [ child ]) -> x :: aux depth child
    | Node (x, childrens) ->
        x
        :: List.concat
             (List.map
                (fun child ->
                  (match child with
                  | Node (y, _) -> create_annotated_ast_bullet depth y.range)
                  :: aux (depth + 1) child)
                childrens)
    (* each bullet need a different id *)
  in
  let res = aux 0 proof_tree in
  { proposition = List.hd res; proof_steps = List.tl res }

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

  let first_proof_tree = List.hd proof_trees in
  let bulleted = add_bullets first_proof_tree in
  print_endline (proof_to_coq_script_string bulleted);
  List.iter
    (fun node ->
      print_endline ("id: " ^ string_of_int node.id ^ " " ^ node.repr))
    (bulleted.proposition :: bulleted.proof_steps);

  let modified = Coq_document.replace_proof bulleted parsed_document in
  match modified with
  | Ok res ->
      List.iter
        (fun node ->
          print_endline "-------------------------";
          print_endline ("id: " ^ string_of_int node.id ^ " " ^ node.repr);
          Lang.Range.pp Format.std_formatter node.range;
          print_newline ();
          print_endline "-------------------------";
          let out = open_out (Filename.remove_extension uri_str ^ "_bis.v") in
          output_string out (Coq_document.dump_to_string res))
        res.elements;

      print_endline (Coq_document.dump_to_string res);
      print_endline "done"
  | Error msg ->
      print_endline "error";
      print_endline msg;
      ()

let main () = Theory.Register.Completed.add dump_ast
let () = main ()
