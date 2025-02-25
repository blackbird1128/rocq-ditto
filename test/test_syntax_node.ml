open Ditto

let pp_int fmt x = Format.fprintf fmt "%d" x

let test_creating_simple () =
  let start_point : Lang.Point.t = { line = 0; character = 0; offset = 0 } in
  let end_point : Lang.Point.t = { line = 0; character = 14; offset = 14 } in
  let range : Lang.Range.t = { start = start_point; end_ = end_point } in
  let node = Syntax_node.syntax_node_of_string "Compute 1 + 1." range in
  Alcotest.(check int) "Hey" 0 0

let tests = [ ("syntax node tests", []) ]
let () = Alcotest.run "syntax node test global" tests
