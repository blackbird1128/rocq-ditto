open Ditto
open Ditto_test_support.Test_support

let test_creating_valid_comment_from_string () =
  let start : Code_point.t = { line = 0; character = 0 } in
  let node = Syntax_node.comment_of_string "(* hello world *)" start in
  let node_repr = Result.map Syntax_node.repr node in

  Alcotest.(
    check
      (result string error_testable)
      "The node should be created without error" (Ok "(* hello world *)")
      node_repr)

let test_creating_invalid_comment_from_string () =
  let node = Syntax_node.comment_of_string "hello world *)" Code_point.dummy in
  let node_repr = Result.map Syntax_node.repr node in

  Alcotest.(
    check
      (result string error_testable)
      "The node creation should not succeed"
      (Error.format_to_or_error
         "Content \"hello world *)\" should start with (*")
      node_repr)

let test_reformat_comment_node () : unit =
  let starting_point : Code_point.t = { line = 0; character = 0 } in

  let comment_node =
    Syntax_node.comment_of_string "(* a comment *)" starting_point
    |> expect_result_ok
  in

  let reformatted_node = Syntax_node.reformat comment_node in
  let reformat_id =
    Result.map (fun (x : Syntax_node.t) -> x.id) reformatted_node
  in

  Alcotest.(check (result uuidm_testable error_testable))
    "Should return an error"
    (Error.string_to_or_error "The node need to have an AST to be reformatted")
    reformat_id

let test_sorting_nodes () : unit =
  let node1 = make_dummy_node_from_repr 0 0 "(* aaaaaa *)" in
  (* your example *)
  let node2 = make_dummy_node_from_repr 0 14 "(*\n*)" in
  (* overlaps with node1 *)
  let node3 = make_dummy_node_from_repr 2 0 "(* aaaa *)" in
  (* does not overlap *)

  let sorted = List.sort Syntax_node.compare [ node2; node3; node1 ] in
  let ids = List.map (fun (n : Syntax_node.t) -> n.id) sorted in

  (* node1 and node2 overlap; smallest common = 18 *)
  (* node1 starts at 16 < 18 => node1 before node2 *)
  (* node3 is later and doesn't overlap *)
  let expected = [ node1.id; node2.id; node3.id ] in

  Alcotest.(check (list uuidm_testable))
    "The nodes should be ordered correctly" expected ids

let test_colliding_nodes_no_common_lines () : unit =
  let target_node = make_dummy_node_from_repr 0 0 "(* aaaaaa *)" in
  let other_node = make_dummy_node_from_repr 1 0 "(* aaaa *)" in

  let colliding_nodes_ids =
    Syntax_node.colliding_nodes target_node [ other_node ]
    |> List.map (fun (node : Syntax_node.t) -> node.id)
  in

  Alcotest.(check (list uuidm_testable))
    "the two nodes should not be colliding" [] colliding_nodes_ids

let test_colliding_nodes_common_line_no_collision () : unit =
  let target_node = make_dummy_node_from_repr 0 0 "(*l*)" in
  let other_node = make_dummy_node_from_repr 0 20 "(*r*)" in

  let colliding_nodes_ids =
    Syntax_node.colliding_nodes target_node [ other_node ]
    |> List.map (fun (node : Syntax_node.t) -> node.id)
  in

  Alcotest.(check (list uuidm_testable))
    "the two nodes should not be colliding" [] colliding_nodes_ids

let test_colliding_nodes_common_line_collision () : unit =
  let target_node = make_dummy_node_from_repr 0 0 "(* hello *)" in
  let other_node = make_dummy_node_from_repr 0 3 "(* world *)" in

  let colliding_nodes_ids =
    Syntax_node.colliding_nodes target_node [ other_node ]
    |> List.map (fun (node : Syntax_node.t) -> node.id)
  in

  Alcotest.(check (list uuidm_testable))
    "the two nodes should be colliding" [ other_node.id ] colliding_nodes_ids

let test_colliding_nodes_multiple_common_lines_collision () : unit =
  let target_node =
    make_dummy_node_from_repr 0 0
      "(*aaaaaaaaa\naaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa*)"
  in
  let other_node =
    make_dummy_node_from_repr 1 12
      "(*aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\naaaaaaaaaaaaaaaaaaaaa*)"
  in

  let colliding_nodes_ids =
    Syntax_node.colliding_nodes target_node [ other_node ]
    |> List.map (fun (node : Syntax_node.t) -> node.id)
  in

  Alcotest.(check (list uuidm_testable))
    "the two nodes should be colliding" [ other_node.id ] colliding_nodes_ids

let tests =
  [
    ( "pure syntax node tests",
      [
        Alcotest.test_case "Check creating a valid comment from a string" `Quick
          test_creating_valid_comment_from_string;
        Alcotest.test_case "Check creating an invalid comment from a string"
          `Quick test_creating_invalid_comment_from_string;
        Alcotest.test_case "Test reformatting a comment node" `Quick
          test_reformat_comment_node;
        Alcotest.test_case "Check if nodes are sorted correctly" `Quick
          test_sorting_nodes;
        Alcotest.test_case
          "Check that two nodes on different lines don't collide" `Quick
          test_colliding_nodes_no_common_lines;
        Alcotest.test_case
          "Check that two nodes on the same line but not overlapping don't \
           overlap"
          `Quick test_colliding_nodes_common_line_no_collision;
        Alcotest.test_case
          "Check that two nodes overlapping on the same line are colliding"
          `Quick test_colliding_nodes_common_line_collision;
        Alcotest.test_case
          "Check that two nodes overlapping on multiple lines are colliding"
          `Quick test_colliding_nodes_multiple_common_lines_collision;
      ] );
  ]

let () = Alcotest.run "Syntax node module tests" tests
