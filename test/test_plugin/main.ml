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

let pp_int fmt x = Format.fprintf fmt "%d" x
let int_tree = testable_nary_tree pp_int ( = )
let proof_status_testable = Alcotest.testable Proof.pp_proof_status ( = )

let test_equality () =
  let tree1 = Node (1, [ Node (2, []); Node (3, [ Node (4, []) ]) ]) in
  let tree2 = Node (1, [ Node (4, []); Node (3, [ Node (4, []) ]) ]) in
  Alcotest.check int_tree "simple tree are not equal, check equality" tree1
    tree2

let create_fixed_test (test_text : string)
    (f : Doc.Node.t list -> string -> string -> unit -> unit)
    (nodes : Doc.Node.t list) (document_text : string) (uri_str : string) =
  Alcotest.test_case test_text `Quick (f nodes document_text uri_str)

let test_parsing_ex1 (nodes : Doc.Node.t list) (document_text : string)
    (uri_str : string) () : unit =
  let doc = Coq_document.parse_document nodes document_text uri_str in
  let nodes_repr = List.map (fun elem -> elem.repr) doc.elements in
  Alcotest.(check int)
    "More than one element was parsed." 1 (List.length nodes_repr);
  Alcotest.(check (list string))
    "parsed element don't match" [ "Compute 1 + 1." ] nodes_repr

let test_parsing_ex2 (nodes : Doc.Node.t list) (document_text : string)
    (uri_str : string) () : unit =
  let doc = Coq_document.parse_document nodes document_text uri_str in
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

let test_proof_parsing_ex2 (nodes : Doc.Node.t list) (document_text : string)
    (uri_str : string) () : unit =
  let doc = Coq_document.parse_document nodes document_text uri_str in
  let proofs = Coq_document.get_proofs doc in
  Alcotest.(check int)
    "The wrong number of proofs was parsed." 1 (List.length proofs);
  let proof = List.hd proofs in
  Alcotest.(check proof_status_testable)
    "The proof should be proved." proof.status Proof.Proved

let test_proof_parsing_name_and_steps_ex2 (nodes : Doc.Node.t list)
    (document_text : string) (uri_str : string) () : unit =
  let doc = Coq_document.parse_document nodes document_text uri_str in
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

let test_proof_parsing_multiple_proofs_ex3 (nodes : Doc.Node.t list)
    (document_text : string) (uri_str : string) () : unit =
  let doc = Coq_document.parse_document nodes document_text uri_str in
  let proofs = Coq_document.get_proofs doc in
  Alcotest.(check int)
    "The wrong number of proofs was parsed" 2 (List.length proofs);
  let proof_names = List.filter_map (fun p -> Proof.get_proof_name p) proofs in
  Alcotest.(check (list string))
    "One or more proof does't have the correct name"
    [ "and_split"; "and_split_bis" ]
    proof_names;
  ()

let test_parsing_comment_ex4 (nodes : Doc.Node.t list) (document_text : string)
    (uri_str : string) () : unit =
  let doc = Coq_document.parse_document nodes document_text uri_str in
  Alcotest.(check int)
    "The wrong number of nodes was parsed" 1 (List.length doc.elements);
  let node = List.hd doc.elements in
  Alcotest.(check string)
    "Comment was badly parsed" "(* single comment *)" node.repr;
  Alcotest.(check bool)
    "Comment node should not have an AST" true (Option.is_empty node.ast)

let test_parsing_multiples_comments_ex5 (nodes : Doc.Node.t list)
    (document_text : string) (uri_str : string) () : unit =
  let doc = Coq_document.parse_document nodes document_text uri_str in
  let comment_nodes =
    List.filter (fun node -> Option.is_empty node.ast) doc.elements
  in
  Alcotest.(check int)
    "The wrong number of comment nodes was parsed" 5
    (List.length comment_nodes);
  Alcotest.(check int)
    "The wrong number of total nodes was parsed" 12 (List.length doc.elements)

let test_parsing_embedded_comments_ex6 (nodes : Doc.Node.t list)
    (document_text : string) (uri_str : string) () : unit =
  let doc = Coq_document.parse_document nodes document_text uri_str in
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

let setup_test_table table (nodes : Doc.Node.t list) (document_text : string)
    (uri_str : string) =
  Hashtbl.add table "ex_parsing1.v"
    (create_fixed_test "test parsing ex 1" test_parsing_ex1 nodes document_text
       uri_str);
  Hashtbl.add table "ex_parsing2.v"
    (create_fixed_test "test parsing ex 2" test_parsing_ex2 nodes document_text
       uri_str);
  Hashtbl.add table "ex_parsing2.v"
    (create_fixed_test "test parsing basic proof properties ex 2"
       test_parsing_ex2 nodes document_text uri_str);
  Hashtbl.add table "ex_parsing2.v"
    (create_fixed_test "test names and steps retrival ex 2"
       test_proof_parsing_name_and_steps_ex2 nodes document_text uri_str);
  Hashtbl.add table "ex_parsing3.v"
    (create_fixed_test "test parsing of two proofs ex3"
       test_proof_parsing_multiple_proofs_ex3 nodes document_text uri_str);
  Hashtbl.add table "ex_parsing4.v"
    (create_fixed_test "test parsing single comment" test_parsing_comment_ex4
       nodes document_text uri_str);
  Hashtbl.add table "ex_parsing5.v"
    (create_fixed_test "test parsing multiple complex comments"
       test_parsing_multiples_comments_ex5 nodes document_text uri_str);
  Hashtbl.add table "ex_parsing6.v"
    (create_fixed_test "test parsing embedded comments"
       test_parsing_embedded_comments_ex6 nodes document_text uri_str);

  ()

let test_runner ~io ~token:_ ~(doc : Doc.t) =
  let test_hash_table = Hashtbl.create 50 in

  let uri_str = Filename.basename (Lang.LUri.File.to_string_uri doc.uri) in
  let document_text = doc.contents.raw in
  let nodes = doc.nodes in
  setup_test_table test_hash_table nodes document_text uri_str;
  let global_tests = Hashtbl.find_all test_hash_table "global" in
  let file_tests = Hashtbl.find_all test_hash_table uri_str in
  let tests = [ ("parsing tests", global_tests @ file_tests) ] in
  print_endline
    ("Running " ^ string_of_int (List.length global_tests) ^ " global tests");
  print_endline
    ("Running "
    ^ string_of_int (List.length file_tests)
    ^ " file test for: " ^ uri_str);
  flush_all ();
  Alcotest.run ~and_exit:true
    ~argv:[| "ignored"; "--color=never" |]
    "document parsing and modification tests" tests;
  ()

let main () = Theory.Register.Completed.add test_runner
let () = main ()
