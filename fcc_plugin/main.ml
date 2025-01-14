open Fleche
open Ditto
open Ditto.Proof_tree
open Ditto.Proof
open Ditto.Annotated_ast_node
open Vernacexpr

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
  ast_node_of_coq_ast ast_node range

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

let replace_by_lia (doc : Doc.t) (proof_tree : annotatedASTNode nary_tree) :
    (Ditto.Proof.proof, string) result =
  let token = Coq.Limits.Token.create () in
  let proof = Proof.tree_to_proof proof_tree in
  let init_state = Proof.get_init_state doc proof in
  let rec aux (st : Petanque.Agent.State.t) (previous_goals : int)
      (node : annotatedASTNode nary_tree) : annotatedASTNode list =
    match node with
    | Node (x, childrens) -> (
        let lia_node =
          Result.get_ok (Annotated_ast_node.ast_node_of_string "lia." x.range)
        in
        let state_x = Petanque.Agent.run ~token ~st ~tac:x.repr () in
        let proof_state_x = Proof.get_proof_state state_x in
        let new_goals = count_goals token proof_state_x in
        let state_lia = Petanque.Agent.run ~token ~st ~tac:lia_node.repr () in
        match state_lia with
        | Ok state_uw ->
            let goals_with_lia = count_goals token state_uw.st in
            if goals_with_lia < previous_goals then
              if goals_with_lia = 0 then
                [ lia_node; qed_ast_node (shift_range 1 0 lia_node.range) ]
              else [ lia_node ]
            else
              x
              :: List.concat (List.map (aux proof_state_x new_goals) childrens)
        | Error err ->
            x :: List.concat (List.map (aux proof_state_x new_goals) childrens))
  in
  match init_state with
  | Some state_err_wrap -> (
      match state_err_wrap with
      | Ok state ->
          let head_tree = top_n 1 proof_tree in
          let tail_tree = List.hd (bottom_n 2 proof_tree) in
          let list = aux state.st 1 tail_tree in
          let list_head_tail = flatten head_tree @ list in
          List.iter (fun x -> print_endline x.repr) (flatten head_tree);
          Ok (Proof.proof_from_nodes list_head_tail)
      | Error err -> Error "failed to create an initial state")
  | None -> Error "can't create an initial state for the proof "

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

  let first_proof_tree = List.nth proof_trees 4 in
  print_tree first_proof_tree " ";

  let bulleted = Result.get_ok (replace_by_lia doc first_proof_tree) in

  let modified = Coq_document.replace_proof bulleted parsed_document in

  match modified with
  | Ok res ->
      List.iter (fun x -> print_endline x.repr) res.elements;
      let out = open_out (Filename.remove_extension uri_str ^ "_bis.v") in

      output_string out (Coq_document.dump_to_string res)
  | Error msg ->
      print_endline "error";
      print_endline msg;
      ()

let main () = Theory.Register.Completed.add dump_ast
let () = main ()
