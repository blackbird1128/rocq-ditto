open Ditto
open Ditto_test_support.Test_support

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
     BasicRubik.v /home/rocq-ditto/_opam/lib/rocq-runtime/rocqworker"
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
     /home/rocq-ditto/_opam/lib/rocq-runtime/rocqworker"
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
     /home/rocq-ditto/_opam/lib/rocq-runtime/rocqworker\n\
     Example.vo Example.glob Example.v.beautified Example.required_vo: \
     Example.v BasicRubik.vo Rubik63.vo Solver.vo \
     /home/rocq-ditto/_opam/lib/rocq-runtime/rocqworker\n\
     Rubik63.vo Rubik63.glob Rubik63.v.beautified Rubik63.required_vo: \
     Rubik63.v BasicRubik.vo /home/rocq-ditto/_opam/lib/rocq-runtime/rocqworker\n\
    \                Solver.vo Solver.glob Solver.v.beautified \
     Solver.required_vo: Solver.v BasicRubik.vo Rubik63.vo \
     /home/rocq-ditto/_opam/lib/rocq-runtime/rocqworker"
  in

  let parsed_output = Compile.parse_depf_output output in
  let assoc_list_res =
    Result.map
      (fun tbl -> Dependency_graph.to_seq tbl |> List.of_seq)
      parsed_output
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

let tests =
  [
    ( "dependency output parsing tests",
      [
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
