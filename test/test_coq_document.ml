open Ditto
open Ditto.Syntax_node

let pp_int fmt x = Format.fprintf fmt "%d" x

let create_dummy_node (range : Lang.Range.t) : syntaxNode =
  {
    ast = None;
    range;
    id = 0;
    repr = "dummy";
    proof_id = None;
    diagnostics = [];
  }

let test_creating_simple () =
  let start_point : Lang.Point.t = { line = 0; character = 0; offset = 0 } in

  let node = Syntax_node.syntax_node_of_string "Compute 1 + 1." start_point in
  Alcotest.(check int) "Hey" 0 0

let tests = [ ("coq document tests", []) ]
let () = Alcotest.run "coq document test global" tests
