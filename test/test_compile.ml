open Ditto
open Ditto_test_support.Test_support

let graph (bindings : ('a * 'b list) list) : ('a, 'b list) Hashtbl.t =
  let table : ('a, 'b list) Hashtbl.t = Hashtbl.create (List.length bindings) in
  List.iter (fun (key, values) -> Hashtbl.replace table key values) bindings;
  table

let dependency_graph_testable =
  Alcotest.slist
    (Alcotest.pair Alcotest.string (Alcotest.list Alcotest.string))
    (fun (key_a, value_a) (key_b, value_b) ->
      let key_comp = String.compare key_a key_b in
      if key_comp = 0 then List.compare String.compare value_a value_b
      else key_comp)

let dependency_rule_testable =
  Alcotest.testable Compile.pp_dependency_rule ( = )

(* rocq dep -f _CoqProject on minirubik project (PI removed) *)
let test_parse_depf_line_without_dependencies () =
  let line =
    "BasicRubik.vo BasicRubik.glob BasicRubik.v.beautified \
     BasicRubik.required_vo: BasicRubik.v \
     /home/rocq-ditto/_opam/lib/rocq-runtime/rocqworker"
  in
  let parsed_line = Compile.parse_depf_line line in

  Alcotest.(check (result dependency_rule_testable error_testable))
    "A line without dependencies should be parsed correctly"
    (Ok { filename = "BasicRubik.v"; dependencies = [] })
    parsed_line

(* rocq dep -f _CoqProject on minirubik project (PI removed) *)
let test_parse_depf_line_with_dependencies () =
  let line =
    "Example.vo Example.glob Example.v.beautified Example.required_vo: \
     Example.v BasicRubik.vo Rubik63.vo Solver.vo \
     /home/rocq-ditto/_opam/lib/rocq-runtime/rocqworker"
  in
  let parsed_line = Compile.parse_depf_line line in
  Alcotest.(check (result dependency_rule_testable error_testable))
    "A line with dependencies should be parsed correctly"
    (Ok
       {
         filename = "Example.v";
         dependencies = [ "BasicRubik.v"; "Rubik63.v"; "Solver.v" ];
       })
    parsed_line

(* rocq dep -f _CoqProject on minirubik project (PI removed) *)
let test_parse_depf_single_dependency () =
  let line =
    "Rubik63.vo Rubik63.glob Rubik63.v.beautified Rubik63.required_vo: \
     Rubik63.v BasicRubik.vo \
     /home/rocq-ditto/_opam/lib/rocq-runtime/rocqworker"
  in
  let parsed_line = Compile.parse_depf_line line in
  Alcotest.(check (result dependency_rule_testable error_testable))
    "A line with a single dependency should be parsed correctly"
    (Ok { filename = "Rubik63.v"; dependencies = [ "BasicRubik.v" ] })
    parsed_line

let test_parse_depf_no_separator () =
  let line =
    "BasicRubik.vo BasicRubik.glob BasicRubik.v.beautified BasicRubik \
     BasicRubik.v \
     /home/alexj/repos/rocq-ditto/_opam/lib/rocq-runtime/rocqworker"
  in
  let parsed_line = Compile.parse_depf_line line in

  Alcotest.(check (result dependency_rule_testable error_testable))
    "A line without a separator should fail to split"
    (Error.format_to_or_error "Can't split the line %S at \"required_vo:\"" line)
    parsed_line

let test_parse_depf_wrong_file_extension () =
  let line =
    "Example.vo Example.glob Example.v.beautified Example.required_vo: \
     Example.v BasicRubik.vok Rubik63.vo Solver.vo \
     /home/alexj/repos/rocq-ditto/_opam/lib/rocq-runtime/rocqworker"
  in
  let parsed_line = Compile.parse_depf_line line in

  Alcotest.(check (result dependency_rule_testable error_testable))
    "A line with a wrong extension on the second part should fail to parse"
    (Error.string_to_or_error "Part: \"BasicRubik.vok\" doesn't end with .vo")
    parsed_line

let test_parse_depf_empty_line () =
  let line = "" in
  let parsed_line = Compile.parse_depf_line line in

  Alcotest.(check (result dependency_rule_testable error_testable))
    ""
    (Error.string_to_or_error "Can't split the line \"\" at \"required_vo:\"")
    parsed_line

let test_parse_depf_output_simple () =
  let output =
    "BasicRubik.vo BasicRubik.glob BasicRubik.v.beautified \
     BasicRubik.required_vo: BasicRubik.v \
     /home/alexj/repos/rocq-ditto/_opam/lib/rocq-runtime/rocqworker\n\
     Example.vo Example.glob Example.v.beautified Example.required_vo: \
     Example.v BasicRubik.vo Rubik63.vo Solver.vo \
     /home/alexj/repos/rocq-ditto/_opam/lib/rocq-runtime/rocqworker\n\
     Rubik63.vo Rubik63.glob Rubik63.v.beautified Rubik63.required_vo: \
     Rubik63.v BasicRubik.vo \
     /home/alexj/repos/rocq-ditto/_opam/lib/rocq-runtime/rocqworker\n\
    \                Solver.vo Solver.glob Solver.v.beautified \
     Solver.required_vo: Solver.v BasicRubik.vo Rubik63.vo \
     /home/alexj/repos/rocq-ditto/_opam/lib/rocq-runtime/rocqworker"
  in

  let parsed_output = Compile.parse_depf_output output in
  let assoc_list_res =
    Result.map (fun tbl -> Hashtbl.to_seq tbl |> List.of_seq) parsed_output
  in

  let expected =
    [
      ("BasicRubik.v", []);
      ("Rubik63.v", [ "BasicRubik.v" ]);
      ("Solver.v", [ "BasicRubik.v"; "Rubik63.v" ]);
      ("Example.v", [ "BasicRubik.v"; "Rubik63.v"; "Solver.v" ]);
    ]
  in

  Alcotest.(check (result dependency_graph_testable error_testable))
    "Simple rocq dep -f should be parsed correctly" (Ok expected) assoc_list_res

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
        Alcotest.test_case
          "Check parsing a single line without dependencies from rocq dep -f"
          `Quick test_parse_depf_line_without_dependencies;
        Alcotest.test_case
          "Check parsing a single line with a single dependency from rocq dep \
           -f"
          `Quick test_parse_depf_single_dependency;
        Alcotest.test_case
          "Check parsing a single line with multiple dependencies from rocq \
           dep -f"
          `Quick test_parse_depf_line_with_dependencies;
        Alcotest.test_case
          "Check parsing a line without a valid separator from rocq dep -f"
          `Quick test_parse_depf_no_separator;
        Alcotest.test_case
          "Check parsing an empty line from rocq dep -f (shouldn't happen)"
          `Quick test_parse_depf_empty_line;
        Alcotest.test_case
          "Check parsing a line with a wrong extension in the second part"
          `Quick test_parse_depf_wrong_file_extension;
        Alcotest.test_case "Check parsing the full output of rocq dep -f" `Quick
          test_parse_depf_output_simple;
      ] );
  ]

let () = Alcotest.run "Compile module tests" tests
