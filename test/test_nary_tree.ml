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
  let tree2 = filter (fun x -> not (x = 4)) tree1 in
  let expected = Node (1, [ Node (2, []); Node (3, []) ]) in
  match tree2 with
  | Some tree ->
      Alcotest.check int_tree
        "the result doesn't have the same shape as the expected result" expected
        tree
  | None -> Alcotest.fail "filter returned None"

let test_filter_multiple () =
  let tree1 =
    Node (24, [ Node (2, []); Node (4, [ Node (6, [ Node (3, []) ]) ]) ])
  in
  let expected = Node (24, [ Node (2, []); Node (4, [ Node (6, []) ]) ]) in
  let tree2 = filter (fun x -> x mod 2 = 0) tree1 in
  match tree2 with
  | Some tree ->
      Alcotest.check int_tree
        "the result doesn't have the same shape as the expected result" expected
        tree
  | None -> Alcotest.fail "filter returned None"

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

let test_depth_first_fold_simple () =
  let tree1 = Node (1, [ Node (2, []); Node (4, [ Node (3, []) ]) ]) in
  let expected = 10 in
  let res = depth_first_fold (fun acc x -> acc + x) 0 tree1 in
  Alcotest.(check int) "result isn't correct" expected res

let test_top_n_simple () =
  let tree1 = Node (1, [ Node (2, []) ]) in
  let expected = Node (1, [ Node (2, []) ]) in
  let res = top_n 1 tree1 in
  Alcotest.check int_tree
    "the result doesn't have the same shape as the expected result" expected res

let test_top_n_n_equal_two () =
  let tree1 = Node (1, [ Node (2, []); Node (4, [ Node (3, []) ]) ]) in
  let expected = Node (1, [ Node (2, []); Node (4, [ Node (3, []) ]) ]) in
  let res = top_n 2 tree1 in
  Alcotest.check int_tree
    "the result doesn't have the same shape as the expected result" expected res

let test_top_n_n_equal_zero () =
  let tree1 = Node (1, [ Node (2, []); Node (3, [ Node (4, []) ]) ]) in
  let expected = Node (1, []) in
  let res = top_n 0 tree1 in
  Alcotest.check int_tree
    "the result doesn't have the same shape as the expected result" expected res

let test_bottom_n_simple () =
  let tree1 = Node (1, [ Node (2, []) ]) in
  let expected = Node (1, [ Node (2, []) ]) in
  let res = bottom_n 0 tree1 in
  Alcotest.check int_tree
    "the result doesn't have the same shape as the expected result" expected
    (List.hd res)

let tests =
  [
    ( "n-ary tree tests",
      [
        Alcotest.test_case "check equality between trees" `Quick test_equality;
        Alcotest.test_case "remove all non matching simple" `Quick
          test_remove_all_non_matching_simple;
        Alcotest.test_case "remove all non matching multiple" `Quick
          test_filter_multiple;
        Alcotest.test_case "flatten a simple tree" `Quick test_flatten_simple;
        Alcotest.test_case "flatten and double each value of a simple tree"
          `Quick test_flatten_map_simple;
        Alcotest.test_case "fold a simple tree" `Quick
          test_depth_first_fold_simple;
        Alcotest.test_case "top_n with n = 1 on a simple tree" `Quick
          test_top_n_simple;
        Alcotest.test_case "top_n with n = 2 on a simple tree" `Quick
          test_top_n_n_equal_two;
        Alcotest.test_case "top_n with n = 0 on a simple tree" `Quick
          test_top_n_n_equal_zero;
        Alcotest.test_case "bottom n with n = 0 on a simple tree" `Quick
          test_bottom_n_simple;
      ] );
  ]

let () = Alcotest.run "N ary tree test global" tests
