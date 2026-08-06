open Ditto

let sorted_string_testable =
  Alcotest.testable
    Fmt.Dump.(list string)
    (fun a b -> List.sort String.compare a = List.sort String.compare b)

let graph (bindings : ('a * 'b list) list) : ('a, 'b list) Hashtbl.t =
  let table : ('a, 'b list) Hashtbl.t = Hashtbl.create (List.length bindings) in
  List.iter (fun (key, values) -> Hashtbl.replace table key values) bindings;
  table

let test_direct_dependencies () =
  let deps = graph [ ("a.v", [ "b.v"; "c.v" ]); ("b.v", []) ] in
  Alcotest.check sorted_string_testable
    "b.v and c.v should be dependencies of a.v" [ "b.v"; "c.v" ]
    (Compile.get_file_dependencies "a.v" deps)

let test_transitive_dependencies () =
  let deps = graph [ ("a.v", [ "b.v"; "c.v" ]); ("b.v", [ "d.v" ]) ] in
  Alcotest.check sorted_string_testable
    "b.v, c.v and d.v should be dependencies of a.v" [ "b.v"; "c.v"; "d.v" ]
    (Compile.get_file_dependencies "a.v" deps)

let test_file_not_in_graph_zero_dependencies () =
  let deps = graph [ ("a.v", [ "b.v"; "c.v" ]); ("b.v", [ "d.v" ]) ] in
  Alcotest.check sorted_string_testable
    "A file not in the graph should not have dependencies" []
    (Compile.get_file_dependencies "z.v" deps)

let test_outdegrees () =
  let deps = graph [ ("a.v", [ "b.v"; "c.v" ]); ("b.v", [ "d.v" ]) ] in
  let outdegrees = Compile.build_outdegrees deps in

  Alcotest.(check int)
    "The out-degree of a.v should be 2" 2
    (Hashtbl.find outdegrees "a.v");
  Alcotest.(check int)
    "The out-degree of b.v should be 1" 1
    (Hashtbl.find outdegrees "b.v");
  Alcotest.(check int)
    "The out-degree of c.v should be 0" 0
    (Hashtbl.find outdegrees "c.v")

let test_outdegrees_outside_graph () =
  let deps = graph [ ("a.v", [ "b.v"; "c.v" ]); ("b.v", [ "d.v" ]) ] in
  let outdegrees = Compile.build_outdegrees deps in

  Alcotest.(check (option int))
    "The out-degree of a node outside the graph should not exists" None
    (Hashtbl.find_opt outdegrees "z.v")

let test_dependents () =
  let deps =
    graph
      [
        ("a.v", [ "b.v"; "c.v" ]); ("b.v", [ "d.v"; "e.v" ]); ("c.v", [ "e.v" ]);
      ]
  in
  let dependents = Compile.build_dependents deps in

  Alcotest.(check (list string))
    "The dependents of a.v should be empty" []
    (Hashtbl.find dependents "a.v");
  Alcotest.(check (list string))
    "The dependents of b.v should be a.v" [ "a.v" ]
    (Hashtbl.find dependents "b.v");
  Alcotest.(check (list string))
    "The dependents of c.v should be a.v" [ "a.v" ]
    (Hashtbl.find dependents "c.v");
  Alcotest.(check (list string))
    "The dependents of d.v should be b.v" [ "b.v" ]
    (Hashtbl.find dependents "d.v");
  Alcotest.(check sorted_string_testable)
    "The dependents of e.v should be b.v and c.v (in any order)"
    [ "b.v"; "c.v" ]
    (Hashtbl.find dependents "e.v")

let test_dependents_outside_graph () =
  let deps = graph [ ("a.v", [ "b.v"; "c.v" ]); ("b.v", [ "d.v" ]) ] in
  let dependents = Compile.build_dependents deps in

  Alcotest.(check (option (list string)))
    "The dependents of a node outside the dependency graph should not exists"
    None
    (Hashtbl.find_opt dependents "z.v")

let tests =
  [
    ( "dependency graph tests",
      [
        Alcotest.test_case "Check getting a simple file dependencies" `Quick
          test_direct_dependencies;
        Alcotest.test_case "Check getting a file dependencies transitively"
          `Quick test_transitive_dependencies;
        Alcotest.test_case
          "Check getting a file dependencies outside the dependencies graph"
          `Quick test_file_not_in_graph_zero_dependencies;
        Alcotest.test_case
          "Check getting the out-degree of each node in a graph" `Quick
          test_outdegrees;
        Alcotest.test_case
          "Check getting the out-degree of a node outside a graph" `Quick
          test_outdegrees_outside_graph;
        Alcotest.test_case
          "Check getting the dependents of each node in a graph" `Quick
          test_dependents;
        Alcotest.test_case
          "Check getting the dependents of a node outside the dependency graph"
          `Quick test_dependents_outside_graph;
      ] );
  ]

let () = Alcotest.run "Compile module tests" tests
