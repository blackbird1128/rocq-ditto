open Ditto.Proof_tree




let testable_nary_tree pp_a equal_a =
  Alcotest.testable (pp_nary_tree pp_a) (equal_nary_tree equal_a)

let pp_int fmt x = Format.fprintf fmt "%d" x
let int_tree = testable_nary_tree pp_int (=)

let test_equality () =
  let tree1 = Node (1, [Node (2, []); Node (3, [Node (4, [])])]) in
  let tree2 = Node (1, [Node (2, []); Node (3, [Node (4, [])])]) in
  Alcotest.check int_tree "simple tree are the same" tree1 tree2

let tests = [
  "n-ary tree tests", [
    Alcotest.test_case "check equality between trees" `Quick test_equality;
  ]
]

let () = Alcotest.run "N ary tree test global" tests

