open Ditto
open Ditto_test_support.Test_support

let test_creating_valid_comment_from_string () =
  let start = Code_point.origin in
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
  let starting_point = Code_point.origin in

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
  let node1 = comment_node_at 0 0 "(* aaaaaa *)" in
  (* your example *)
  let node2 = comment_node_at 0 14 "(*\n*)" in
  (* overlaps with node1 *)
  let node3 = comment_node_at 2 0 "(* aaaa *)" in
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
  let target_node = comment_node_at 0 0 "(* aaaaaa *)" in
  let other_node = comment_node_at 1 0 "(* aaaa *)" in

  let colliding_nodes_ids =
    Syntax_node.colliding_nodes target_node [ other_node ]
    |> List.map (fun (node : Syntax_node.t) -> node.id)
  in

  Alcotest.(check (list uuidm_testable))
    "the two nodes should not be colliding" [] colliding_nodes_ids

let test_colliding_nodes_common_line_no_collision () : unit =
  let target_node = comment_node_at 0 0 "(*l*)" in
  let other_node = comment_node_at 0 20 "(*r*)" in

  let colliding_nodes_ids =
    Syntax_node.colliding_nodes target_node [ other_node ]
    |> List.map (fun (node : Syntax_node.t) -> node.id)
  in

  Alcotest.(check (list uuidm_testable))
    "the two nodes should not be colliding" [] colliding_nodes_ids

let test_colliding_nodes_common_line_collision () : unit =
  let target_node = comment_node_at 0 0 "(* hello *)" in
  let other_node = comment_node_at 0 3 "(* world *)" in

  let colliding_nodes_ids =
    Syntax_node.colliding_nodes target_node [ other_node ]
    |> List.map (fun (node : Syntax_node.t) -> node.id)
  in

  Alcotest.(check (list uuidm_testable))
    "the two nodes should be colliding" [ other_node.id ] colliding_nodes_ids

let test_colliding_nodes_multiple_common_lines_collision () : unit =
  let target_node =
    comment_node_at 0 0 "(*aaaaaaaaa\naaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa*)"
  in
  let other_node =
    comment_node_at 1 12
      "(*aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\naaaaaaaaaaaaaaaaaaaaa*)"
  in

  let colliding_nodes_ids =
    Syntax_node.colliding_nodes target_node [ other_node ]
    |> List.map (fun (node : Syntax_node.t) -> node.id)
  in

  Alcotest.(check (list uuidm_testable))
    "the two nodes should be colliding" [ other_node.id ] colliding_nodes_ids

let test_move_to_single_line_node_horizontal_move () : unit =
  let start_point = point ~line:3 ~char:4 in
  let comment_repr = "(* hello world *)" in

  let node_to_move = comment_node ~start:start_point comment_repr in
  let destination = point ~line:3 ~char:7 in

  let moved_node = Syntax_node.move_to destination node_to_move in
  let expected_range =
    range ~start:destination ~end_:(point ~line:3 ~char:24)
  in

  Alcotest.(check range_testable)
    "The two ranges should be equal" expected_range moved_node.range

let test_move_to_single_line_node_vertical_move () : unit =
  let start_point = point ~line:3 ~char:4 in
  let comment_repr = "(* hello world  *)" in

  let node_to_move = comment_node ~start:start_point comment_repr in
  let destination = point ~line:5 ~char:5 in

  let moved_node = Syntax_node.move_to destination node_to_move in
  let expected_range =
    range ~start:destination ~end_:(point ~line:5 ~char:23)
  in

  Alcotest.(check range_testable)
    "The two ranges should be equal" expected_range moved_node.range

let test_move_to_multiline_node_horizontal_move () : unit =
  let start_point = point ~line:3 ~char:4 in
  let comment_repr = "(* hello world\nfrom a multi-lines comment *)" in

  let node_to_move = comment_node ~start:start_point comment_repr in

  let destination = point ~line:3 ~char:7 in

  let moved_node = Syntax_node.move_to destination node_to_move in
  let expected_range =
    range ~start:destination ~end_:(point ~line:4 ~char:29)
  in

  Alcotest.(check range_testable)
    "The two ranges should be equal" expected_range moved_node.range

let test_move_to_range_prop =
  QCheck.Test.make ~count:1000
    ~name:"move_to computes the range from the destination and representation"
    QCheck.(pair comment_node_arbitrary point_arbitrary)
    (fun (node, destination) ->
      let moved = Syntax_node.move_to destination node in
      let expected =
        Code_range.extent_of_string destination (Syntax_node.repr node)
      in
      Code_range.equal moved.range expected && Uuidm.equal moved.id node.id)

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
        Alcotest.test_case
          "Test moving a single-line node horizontally" `Quick
          test_move_to_single_line_node_horizontal_move;
        Alcotest.test_case
          "Test moving a single-line node vertically" `Quick
          test_move_to_single_line_node_vertical_move;
        Alcotest.test_case "Test moving a multiline node horizontally" `Quick
          test_move_to_multiline_node_horizontal_move;
        QCheck_alcotest.to_alcotest test_move_to_range_prop;
      ] );
  ]

let () = Alcotest.run "Syntax node module tests" tests
