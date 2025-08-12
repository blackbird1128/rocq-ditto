open Ditto
open Ditto.Syntax_node

let pp_int fmt x = Format.fprintf fmt "%d" x

let create_dummy_node (range : Code_range.t) : syntaxNode =
  {
    ast = None;
    range;
    id = Unique_id.uuid ();
    repr = "dummy";
    proof_id = None;
    diagnostics = [];
  }

let tests = [ ("coq document tests", []) ]
let () = Alcotest.run "coq document test global" tests
