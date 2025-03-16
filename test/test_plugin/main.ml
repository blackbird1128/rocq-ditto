open Fleche
open Ditto
open Ditto.Proof_tree
open Ditto.Proof
open Ditto.Syntax_node
open Vernacexpr

let normalize_strings (strings : string list) : string list =
  List.map (fun str -> String.trim str) strings

let testable_nary_tree pp_a equal_a =
  Alcotest.testable (pp_nary_tree pp_a) (equal_nary_tree equal_a)

let document_to_range_representation_pairs (doc : Coq_document.t) :
    (string * Lang.Range.t) list =
  List.map (fun node -> (node.repr, node.range)) doc.elements

let parse_json_target (json : Yojson.Safe.t) : (string * Lang.Range.t) list =
  let open Yojson.Safe.Util in
  json |> to_list
  |> List.map (fun elem ->
         let range = range_of_yojson (member "range" elem) in
         let repr = to_string (member "repr" elem) in
         (repr, range))

let get_target (uri_str : string) =
  let uri_str_without_ext = Filename.remove_extension uri_str in
  let target = uri_str_without_ext ^ "_target.v.target.json" in
  let target_doc = Yojson.Safe.from_file target in
  parse_json_target target_doc

let pp_int fmt x = Format.fprintf fmt "%d" x
let int_tree = testable_nary_tree pp_int ( = )
let proof_status_testable = Alcotest.testable Proof.pp_proof_status ( = )
let range_testable = Alcotest.testable Lang.Range.pp ( = )

let create_fixed_test (test_text : string) (f : Doc.t -> unit -> unit)
    (doc : Doc.t) =
  Alcotest.test_case test_text `Quick (f doc)

let test_creating_simple_node (doc : Doc.t) () : unit =
  let start_point : Lang.Point.t = { line = 0; character = 0; offset = 0 } in
  let end_point : Lang.Point.t = { line = 0; character = 14; offset = 14 } in
  let range : Lang.Range.t = { start = start_point; end_ = end_point } in
  let node = Syntax_node.syntax_node_of_string "Compute 1 + 1." range in
  let node_res_repr = Result.map (fun node -> node.repr) node in
  Alcotest.(check (result string string))
    "The syntax node should have the same representation" (Ok "Compute 1 + 1.")
    node_res_repr

let test_creating_node_with_incorrect_range_char (doc : Doc.t) () : unit =
  let start_point : Lang.Point.t = { line = 0; character = 0; offset = 0 } in
  let end_point : Lang.Point.t = { line = 0; character = 8; offset = 14 } in
  let range : Lang.Range.t = { start = start_point; end_ = end_point } in
  let node = Syntax_node.syntax_node_of_string "Compute 1 + 1." range in
  let node_res_repr = Result.map (fun node -> node.repr) node in
  Alcotest.(check (result string string))
    "The syntax node should have the same representation"
    (Error
       "Incorrect range: range end character minus range start character \
        smaller than node character size")
    node_res_repr

let test_creating_node_with_incorrect_range_offset (doc : Doc.t) () : unit =
  let start_point : Lang.Point.t = { line = 0; character = 0; offset = 0 } in
  let end_point : Lang.Point.t = { line = 0; character = 14; offset = 8 } in
  let range : Lang.Range.t = { start = start_point; end_ = end_point } in
  let node = Syntax_node.syntax_node_of_string "Compute 1 + 1." range in
  let node_res_repr = Result.map (fun node -> node.repr) node in
  Alcotest.(check (result string string))
    "The syntax node should have the same representation"
    (Error
       "Incorrect range: range end offset minus range start offset smaller \
        than node character size")
    node_res_repr

let test_parsing_logical_id_assignement (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in
  let _ =
    List.fold_left
      (fun id_acc node ->
        Alcotest.(check int) "Id doesn't match the " id_acc node.id;
        id_acc + 1)
      0 doc.elements
  in
  ()

let test_parsing_ex1 (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in
  let nodes_repr = List.map (fun elem -> elem.repr) doc.elements in
  Alcotest.(check int)
    "More than one element was parsed." 1 (List.length nodes_repr);
  Alcotest.(check (list string))
    "parsed element don't match" [ "Compute 1 + 1." ] nodes_repr

let test_parsing_ex2 (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in
  let nodes_repr = List.map (fun elem -> elem.repr) doc.elements in
  Alcotest.(check int)
    "The wrong number of elements was parsed" 7 (List.length nodes_repr);
  Alcotest.(check (list string))
    "parsed element don't match"
    [
      "Theorem modus_ponens:\n  forall A B: Prop, A /\\ (A -> B) -> B.";
      "Proof.";
      "intros.";
      "destruct H as [H1 H2].";
      "apply H2.";
      "assumption.";
      "Qed.";
    ]
    nodes_repr

let test_proof_parsing_ex2 (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in
  let proofs = Coq_document.get_proofs doc in
  Alcotest.(check int)
    "The wrong number of proofs was parsed." 1 (List.length proofs);
  let proof = List.hd proofs in
  Alcotest.(check proof_status_testable)
    "The proof should be proved." Proof.Proved proof.status

let test_parsing_admit (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in
  let proofs = Coq_document.get_proofs doc in
  Alcotest.(check int)
    "The wrong number of proofs was parsed." 1 (List.length proofs);
  let proof = List.hd proofs in
  Alcotest.check proof_status_testable "The proof should be admitted."
    Proof.Admitted proof.status

let test_parsing_defined (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in
  let proofs = Coq_document.get_proofs doc in
  Alcotest.(check int)
    "The wrong number of proofs was parsed." 1 (List.length proofs);
  let proof = List.hd proofs in
  Alcotest.check proof_status_testable "The proof should be proved."
    Proof.Proved proof.status

let test_parsing_function (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in
  let proofs = Coq_document.get_proofs doc in
  Alcotest.(check int)
    "The wrong number of proofs was parsed." 1 (List.length proofs);
  let proof = List.hd proofs in
  Alcotest.check proof_status_testable "The proof should be proved."
    Proof.Proved proof.status

let test_parsing_abort1 (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in
  let proofs = Coq_document.get_proofs doc in
  Alcotest.(check int)
    "The wrong number of proofs was parsed." 1 (List.length proofs);
  let proof = List.hd proofs in
  Alcotest.check proof_status_testable "The proof should be aborted."
    Proof.Aborted proof.status

let test_parsing_abort2 (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in
  let proofs = Coq_document.get_proofs doc in
  Alcotest.(check int)
    "The wrong number of proofs was parsed." 2 (List.length proofs);
  let first_proof = List.hd proofs in
  let second_proof = List.nth proofs 1 in
  Alcotest.check proof_status_testable "The first proof should be aborted"
    Proof.Aborted first_proof.status;
  Alcotest.check proof_status_testable "The second proof is proved" Proof.Proved
    second_proof.status

let test_proof_parsing_name_and_steps_ex2 (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in
  let proof = List.hd (Coq_document.get_proofs doc) in
  Alcotest.(check string)
    "The proof name should be modus ponens" "modus_ponens"
    (Option.default "got none" (Proof.get_proof_name proof));
  Alcotest.(check int)
    "The proof should have 6 steps (including Proof. and Qed.)" 6
    (List.length proof.proof_steps);
  Alcotest.(check string)
    "The proof expression is wrong."
    "Theorem modus_ponens:\n  forall A B: Prop, A /\\ (A -> B) -> B."
    proof.proposition.repr;
  let proof_steps_normalized =
    normalize_strings (List.map (fun s -> s.repr) proof.proof_steps)
  in
  Alcotest.(check (list string))
    "The proof should have the following steps."
    [
      "Proof.";
      "intros.";
      "destruct H as [H1 H2].";
      "apply H2.";
      "assumption.";
      "Qed.";
    ]
    proof_steps_normalized

let test_proof_parsing_multiple_proofs_ex3 (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in
  let proofs = Coq_document.get_proofs doc in
  Alcotest.(check int)
    "The wrong number of proofs was parsed" 2 (List.length proofs);
  let proof_names = List.filter_map (fun p -> Proof.get_proof_name p) proofs in
  Alcotest.(check (list string))
    "One or more proof does't have the correct name"
    [ "and_split"; "and_split_bis" ]
    proof_names;
  ()

let test_parsing_comment_ex4 (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in
  Alcotest.(check int)
    "The wrong number of nodes was parsed" 1 (List.length doc.elements);
  let node = List.hd doc.elements in
  Alcotest.(check string)
    "Comment was badly parsed" "(* single comment *)" node.repr;
  Alcotest.(check bool)
    "Comment node should not have an AST" true (Option.is_empty node.ast)

let test_parsing_multiples_comments_ex5 (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in
  let comment_nodes =
    List.filter (fun node -> Option.is_empty node.ast) doc.elements
  in
  Alcotest.(check int)
    "The wrong number of comment nodes was parsed" 5
    (List.length comment_nodes);
  Alcotest.(check int)
    "The wrong number of total nodes was parsed" 12 (List.length doc.elements)

let test_parsing_embedded_comments_ex6 (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in
  let comment_nodes =
    List.filter (fun node -> Option.is_empty node.ast) doc.elements
  in
  let comment_nodes_repr = List.map (fun node -> node.repr) comment_nodes in
  Alcotest.(check int)
    "The wrong number of comment nodes was parsed" 2
    (List.length comment_nodes);
  Alcotest.(check (list string))
    "Comments badly parsed"
    [ "(* in the same line comment *)"; "(* classical comment *)" ]
    comment_nodes_repr

let test_parsing_weird_comments_ex7 (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in
  let comment_nodes =
    List.filter (fun node -> Option.is_empty node.ast) doc.elements
  in
  let comment_nodes_repr = List.map (fun node -> node.repr) comment_nodes in
  print_endline
    ("comment nodes length : " ^ string_of_int (List.length comment_nodes));
  Alcotest.(check int)
    "The wrong number of comment nodes was parsed" 2
    (List.length comment_nodes);
  Alcotest.(check (list string))
    "Comments badly parsed"
    [ "(*in the same line comment*)"; "(**weird comment*)" ]
    comment_nodes_repr

let test_parsing_instance (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in

  let proofs = Coq_document.get_proofs doc in
  Alcotest.(check int)
    "The wrong number of proofs was parsed." 1 (List.length proofs);
  let first_proof = List.hd proofs in
  Alcotest.check proof_status_testable "The proof should be proved" Proof.Proved
    first_proof.status

let test_searching_node (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in
  List.iter
    (fun elem -> Format.printf "id:%d repr:%s @ " elem.id elem.repr)
    doc.elements;
  let node_compute = Coq_document.element_with_id_opt 0 doc in
  let node_compute_id = Option.map (fun node -> node.id) node_compute in
  Alcotest.(check (option int))
    "Item with the wrong id was retrieved" (Some 0) node_compute_id;
  Alcotest.(check (option string))
    "The wrong repr was retrieved" (Some "Compute 1.")
    (Option.map (fun node -> node.repr) node_compute);
  let absurd_node = Coq_document.element_with_id_opt (-1) doc in
  Alcotest.(check (option int))
    "No element should be retrieved" None
    (Option.map (fun x -> x.id) absurd_node)

let test_removing_only_node_on_line (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Coq_document.parse_document doc in

  let parsed_target = get_target uri_str in

  let new_doc = Coq_document.remove_node_with_id 0 doc in
  let new_doc_res = document_to_range_representation_pairs new_doc in

  Alcotest.(check (list (pair string range_testable)))
    "The two lists should be the same" parsed_target new_doc_res

let test_removing_multiple_line_node (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Coq_document.parse_document doc in

  let parsed_target = get_target uri_str in

  let new_doc = Coq_document.remove_node_with_id 1 doc in
  let new_doc_res = document_to_range_representation_pairs new_doc in

  Alcotest.(check (list (pair string range_testable)))
    "The two lists should be the same" parsed_target new_doc_res

let test_removing_node_same_line_as_other (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Coq_document.parse_document doc in
  let parsed_target = get_target uri_str in
  let new_doc = Coq_document.remove_node_with_id 1 doc in
  let new_doc_res = document_to_range_representation_pairs new_doc in
  Alcotest.(check (list (pair string range_testable)))
    "The two lists should be the same" parsed_target new_doc_res

let test_adding_node_on_empty_line (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Coq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Lang.Point.t = { line = 1; character = 0; offset = 11 } in
  let end_point : Lang.Point.t = { line = 1; character = 10; offset = 21 } in
  let node_range : Lang.Range.t = { start = start_point; end_ = end_point } in
  let node =
    Result.get_ok (Syntax_node.syntax_node_of_string "Compute 2." node_range)
  in
  let new_doc = Coq_document.insert_node node doc in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in

  Alcotest.(check (result (list (pair string range_testable)) string))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_adding_node_before_busy_line (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Coq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Lang.Point.t = { line = 1; character = 0; offset = 11 } in
  let end_point : Lang.Point.t = { line = 1; character = 10; offset = 21 } in
  let node_range : Lang.Range.t = { start = start_point; end_ = end_point } in
  let node =
    Result.get_ok (Syntax_node.syntax_node_of_string "Compute 2." node_range)
  in

  let new_doc = Coq_document.insert_node node doc in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in

  Alcotest.(check (result (list (pair string range_testable)) string))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_adding_multiple_line_node (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Coq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Lang.Point.t = { line = 2; character = 0; offset = 12 } in
  let end_point : Lang.Point.t = { line = 4; character = 10; offset = 42 } in
  let node_range : Lang.Range.t = { start = start_point; end_ = end_point } in
  let node =
    Result.get_ok
      (Syntax_node.syntax_node_of_string "Compute 1\n        +\n        1."
         node_range)
  in

  let new_doc = Coq_document.insert_node node doc in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in

  Alcotest.(check (result (list (pair string range_testable)) string))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_adding_node_between (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Coq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Lang.Point.t = { line = 1; character = 11; offset = 12 } in
  let end_point : Lang.Point.t = { line = 1; character = 21; offset = 22 } in
  let node_range : Lang.Range.t = { start = start_point; end_ = end_point } in
  let node =
    Result.get_ok (Syntax_node.syntax_node_of_string "Compute 2." node_range)
  in

  let new_doc =
    Coq_document.insert_node ~shift_method:ShiftHorizontally node doc
  in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in

  Alcotest.(check (result (list (pair string range_testable)) string))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_adding_collision_next_line (doc : Doc.t) () : unit =
  (* TODO bugged for now, fix later *)
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Coq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Lang.Point.t = { line = 2; character = 0; offset = 12 } in
  let end_point : Lang.Point.t = { line = 4; character = 2; offset = 26 } in
  let node_range : Lang.Range.t = { start = start_point; end_ = end_point } in
  let node =
    Result.get_ok
      (Syntax_node.syntax_node_of_string "Compute 1\n+\n1." node_range)
  in

  let new_doc = Coq_document.insert_node node doc in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in

  Alcotest.(check (result (list (pair string range_testable)) string))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_replacing_single_node_on_line (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Coq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Lang.Point.t = { line = 2; character = 0; offset = 12 } in
  let end_point : Lang.Point.t = { line = 2; character = 11; offset = 23 } in
  let node_range : Lang.Range.t = { start = start_point; end_ = end_point } in
  let node =
    Result.get_ok (Syntax_node.syntax_node_of_string "Compute 42." node_range)
  in

  let new_doc = Coq_document.replace_node 1 node doc in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in

  Alcotest.(check (result (list (pair string range_testable)) string))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_replacing_first_node_on_line (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Coq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Lang.Point.t = { line = 2; character = 0; offset = 12 } in
  let end_point : Lang.Point.t = { line = 2; character = 12; offset = 24 } in
  let node_range : Lang.Range.t = { start = start_point; end_ = end_point } in
  let node =
    Result.get_ok (Syntax_node.syntax_node_of_string "Compute 123." node_range)
  in

  let new_doc = Coq_document.replace_node 1 node doc in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in

  Alcotest.(check (result (list (pair string range_testable)) string))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_replacing_node_in_middle_of_line (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Coq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Lang.Point.t = { line = 2; character = 11; offset = 23 } in
  let end_point : Lang.Point.t = { line = 2; character = 26; offset = 38 } in
  let node_range : Lang.Range.t = { start = start_point; end_ = end_point } in
  let node =
    Result.get_ok
      (Syntax_node.syntax_node_of_string "Compute 123456." node_range)
  in

  let new_doc = Coq_document.replace_node 2 node doc in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in

  Alcotest.(check (result (list (pair string range_testable)) string))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_replacing_node_end_of_line (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Coq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Lang.Point.t = { line = 2; character = 22; offset = 34 } in
  let end_point : Lang.Point.t = { line = 2; character = 36; offset = 48 } in
  let node_range : Lang.Range.t = { start = start_point; end_ = end_point } in
  let node =
    Result.get_ok
      (Syntax_node.syntax_node_of_string "Compute 12345." node_range)
  in

  let new_doc = Coq_document.replace_node 3 node doc in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in

  Alcotest.(check (result (list (pair string range_testable)) string))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_adding_removing_nodes_simple (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in
  let parsed_target = document_to_range_representation_pairs doc in

  let empty_doc =
    List.fold_left
      (fun doc_acc node -> Coq_document.remove_node_with_id node.id doc)
      doc doc.elements
  in
  ()
(* abort for now as we still rely on the old definition of insert *)
(* TODO complete *)

let setup_test_table table (doc : Doc.t) =
  Hashtbl.add table "test_dummy.v"
    (create_fixed_test "Check if a simple test is created normally"
       test_creating_simple_node doc);
  Hashtbl.add table "test_dummy.v"
    (create_fixed_test "Check if a wrong character range trigger an error"
       test_creating_node_with_incorrect_range_char doc);
  Hashtbl.add table "test_dummy.v"
    (create_fixed_test "Check if a wrong offset range trigger an error"
       test_creating_node_with_incorrect_range_offset doc);
  Hashtbl.add table "ex_id_assign1.v"
    (create_fixed_test "check if id are assigned logically 1"
       test_parsing_logical_id_assignement doc);
  Hashtbl.add table "ex_id_assign2.v"
    (create_fixed_test "check if id are assigned logically 2"
       test_parsing_logical_id_assignement doc);
  Hashtbl.add table "ex_id_assign3.v"
    (create_fixed_test "check if id are assigned logically 3"
       test_parsing_logical_id_assignement doc);

  Hashtbl.add table "ex_parsing1.v"
    (create_fixed_test "test parsing ex 1" test_parsing_ex1 doc);
  Hashtbl.add table "ex_parsing2.v"
    (create_fixed_test "test parsing ex 2" test_parsing_ex2 doc);
  Hashtbl.add table "ex_parsing2.v"
    (create_fixed_test "test parsing basic proof properties ex 2"
       test_parsing_ex2 doc);
  Hashtbl.add table "ex_admit.v"
    (create_fixed_test "test parsing admitted proof" test_parsing_admit doc);
  Hashtbl.add table "ex_defined1.v"
    (create_fixed_test "test parsing defined proof" test_parsing_defined doc);
  Hashtbl.add table "ex_function1.v"
    (create_fixed_test "test parsing function proof" test_parsing_function doc);
  Hashtbl.add table "ex_abort1.v"
    (create_fixed_test "test parsing aborted proof 1" test_parsing_abort1 doc);
  Hashtbl.add table "ex_abort2.v"
    (create_fixed_test "test parsing aborted proof 2" test_parsing_abort2 doc);
  Hashtbl.add table "ex_instance1.v"
    (create_fixed_test "test parsing an instance proof" test_parsing_instance
       doc);
  Hashtbl.add table "ex_parsing2.v"
    (create_fixed_test "test names and steps retrival ex 2"
       test_proof_parsing_name_and_steps_ex2 doc);
  Hashtbl.add table "ex_parsing3.v"
    (create_fixed_test "test parsing of two proofs ex3"
       test_proof_parsing_multiple_proofs_ex3 doc);
  Hashtbl.add table "ex_parsing4.v"
    (create_fixed_test "test parsing single comment" test_parsing_comment_ex4
       doc);
  Hashtbl.add table "ex_parsing5.v"
    (create_fixed_test "test parsing multiple complex comments"
       test_parsing_multiples_comments_ex5 doc);
  Hashtbl.add table "ex_parsing6.v"
    (create_fixed_test "test parsing embedded comments"
       test_parsing_embedded_comments_ex6 doc);
  Hashtbl.add table "ex_parsing7.v"
    (create_fixed_test "test parsing weird comments"
       test_parsing_weird_comments_ex7 doc);

  Hashtbl.add table "ex_removing1.v"
    (create_fixed_test "test removing only node on a line"
       test_removing_only_node_on_line doc);
  Hashtbl.add table "ex_removing2.v"
    (create_fixed_test "test removing a node spanning multiple lines"
       test_removing_multiple_line_node doc);
  Hashtbl.add table "ex_removing3.v"
    (create_fixed_test "test removing a node on the same line as another one"
       test_removing_node_same_line_as_other doc);
  Hashtbl.add table "ex_adding1.v"
    (create_fixed_test "test searching node" test_searching_node doc);
  Hashtbl.add table "ex_adding1.v"
    (create_fixed_test "test adding new nodes on an empty line"
       test_adding_node_on_empty_line doc);
  Hashtbl.add table "ex_adding2.v"
    (create_fixed_test "test adding new node on a filled line"
       test_adding_node_before_busy_line doc);
  Hashtbl.add table "ex_adding3.v"
    (create_fixed_test "test adding a new node spanning multiple lines"
       test_adding_multiple_line_node doc);
  Hashtbl.add table "ex_adding4.v"
    (create_fixed_test "test adding a node between two nodes on the same line"
       test_adding_node_between doc);
  (* TODO fix Hashtbl.add table "ex_adding5.v"
    (create_fixed_test "test adding a node that will collide on another line"
       test_adding_collision_next_line doc); *)
  Hashtbl.add table "ex_replacing1.v"
    (create_fixed_test "test replacing the single node on one line"
       test_replacing_single_node_on_line doc);
  Hashtbl.add table "ex_replacing2.v"
    (create_fixed_test "test replacing the first node on one line"
       test_replacing_first_node_on_line doc);
  Hashtbl.add table "ex_replacing3.v"
    (create_fixed_test "test replacing a node in the middle of a line"
       test_replacing_node_in_middle_of_line doc);
  Hashtbl.add table "ex_replacing4.v"
    (create_fixed_test "test replacing a node with some spaces after"
       test_replacing_node_end_of_line doc);
  ()

let test_runner ~io ~token:_ ~(doc : Doc.t) =
  let test_hash_table = Hashtbl.create 50 in

  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let uri_name_str = Filename.basename uri_str in
  let document_text = doc.contents.raw in
  let nodes = doc.nodes in
  setup_test_table test_hash_table doc;
  let global_tests = Hashtbl.find_all test_hash_table "global" in
  let file_tests = Hashtbl.find_all test_hash_table uri_name_str in
  let tests = [ ("parsing tests", global_tests @ file_tests) ] in
  print_endline
    ("Running " ^ string_of_int (List.length global_tests) ^ " global tests");
  print_endline
    ("Running "
    ^ string_of_int (List.length file_tests)
    ^ " file test for: " ^ uri_name_str);
  flush_all ();
  Alcotest.run ~and_exit:true
    ~argv:[| "ignored"; "--color=always" |]
    "document parsing and modification tests" tests;
  ()

let main () = Theory.Register.Completed.add test_runner
let () = main ()
