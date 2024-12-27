open Ditto.Proof_tree

let testable_nary_tree pp_a equal_a =
  Alcotest.testable (pp_nary_tree pp_a) (equal_nary_tree equal_a)

let pp_int fmt x = Format.fprintf fmt "%d" x
let int_tree = testable_nary_tree pp_int ( = )

let test_equality () =
  let tree1 = Node (1, [ Node (2, []); Node (3, [ Node (4, []) ]) ]) in
  let tree2 = Node (1, [ Node (2, []); Node (3, [ Node (4, []) ]) ]) in
  Alcotest.check int_tree "simple tree are not equal, check equality" tree1
    tree2

let test_remove_all_non_matching_simple () =
  let tree1 = Node (1, [ Node (2, []); Node (4, [ Node (3, []) ]) ]) in
  let tree2 = remove_all_nonmatching (fun x -> not (x = 4)) tree1 in
  let expected = Node (1, [ Node (2, []); Node (3, []) ]) in
  match tree2 with
  | Some tree ->
      Alcotest.check int_tree
        "the result doesn't have the same shape as the expected result" expected
        tree
  | None -> Alcotest.fail "remove_all_nonmatching returned None"

let test_remove_all_nonmatching_multiple () =
  let tree1 =
    Node (24, [ Node (2, []); Node (4, [ Node (6, [ Node (3, []) ]) ]) ])
  in
  let expected = Node (24, [ Node (2, []); Node (4, [ Node (6, []) ]) ]) in
  let tree2 = remove_all_nonmatching (fun x -> x mod 2 = 0) tree1 in
  match tree2 with
  | Some tree ->
      Alcotest.check int_tree
        "the result doesn't have the same shape as the expected result" expected
        tree
  | None -> Alcotest.fail "remove_all_nonmatching returned None"

let test_flatten_simple () =
  let tree1 = Node (1, [ Node (2, []); Node (4, [ Node (3, []) ]) ]) in
  let expected = [ 1; 2; 4; 3 ] in
  let flattened = flatten tree1 in
  Alcotest.(check (list int))
    "the result doesn't have the same shape at the expected result" expected
    flattened

let test_flatten_map_simple () =
  let tree1 = Node (1, [ Node (2, []); Node (4, [ Node (3, []) ]) ]) in
  let expected = [ 2; 4; 8; 6 ] in
  let flattened_map = flatten_map (fun x -> 2 * x) tree1 in
  Alcotest.(check (list int))
    "the result doesn't have the same shape at the expected result" expected
    flattened_map

let tests =
  [
    ( "n-ary tree tests",
      [
        Alcotest.test_case "check equality between trees" `Quick test_equality;
        Alcotest.test_case "remove all non matching simple" `Quick
          test_remove_all_non_matching_simple;
        Alcotest.test_case "remove all non matching multiple" `Quick
          test_remove_all_nonmatching_multiple;
        Alcotest.test_case "flatten a simple tree" `Quick test_flatten_simple;
        Alcotest.test_case "flatten and double each value of a simple tree"
          `Quick test_flatten_map_simple;
      ] );
  ]

let () = Alcotest.run "N ary tree test global" tests
