open Fleche
open Ditto
open Ditto.Proof_tree
open Ditto.Proof
open Ditto.Syntax_node
open Vernacexpr

let testable_nary_tree pp_a equal_a =
  Alcotest.testable (pp_nary_tree pp_a) (equal_nary_tree equal_a)

let pp_int fmt x = Format.fprintf fmt "%d" x
let int_tree = testable_nary_tree pp_int ( = )

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

let setup_test_table table (nodes : Doc.Node.t list) (document_text : string)
    (uri_str : string) =
  Hashtbl.add table "ex_parsing1.v"
    (create_fixed_test "test parsing ex 1" test_parsing_ex1 nodes document_text
       uri_str);
  Hashtbl.add table "ex_parsing2.v"
    (create_fixed_test "test parsing ex 2" test_parsing_ex2 nodes document_text
       uri_str)

let test_runner ~io ~token:_ ~(doc : Doc.t) =
  let test_hash_table = Hashtbl.create 50 in

  let uri_str = Filename.basename (Lang.LUri.File.to_string_uri doc.uri) in
  let document_text = doc.contents.raw in
  let lvl = Io.Level.Info in
  Io.Report.msg ~io ~lvl "[ast plugin] dumping ast for %s ..." uri_str;
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
  Alcotest.run ~and_exit:false
    ~argv:[| "ignored"; "--color=never" |]
    ~compact:true "document parsing and modification tests" tests;
  ()

let main () = Theory.Register.Completed.add test_runner
let () = main ()
