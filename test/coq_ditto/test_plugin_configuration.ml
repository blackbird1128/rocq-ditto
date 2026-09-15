open Ditto_cli_lib.Plugin_configuration

(* let dependencies_action_gen = *)
(*   QCheck.Gen.oneof_list [ NoAction; CompileDependencies; TransformDependencies ] *)

let output_format_gen = QCheck.Gen.oneof_list [ Text; Json ]

let output_format_arbitrary =
  QCheck.make ~print:output_format_to_string output_format_gen

let transformation_kind_gen = QCheck.Gen.oneof_list all_transformation_kinds

let transformation_kind_arbitrary =
  QCheck.make ~print:transformation_kind_to_string transformation_kind_gen

let statistic_kind_gen = QCheck.Gen.oneof_list all_statistic_kinds

let statistic_kind_arbitrary =
  QCheck.make ~print:statistic_kind_to_string statistic_kind_gen

let test_camel_to_snake_simple () =
  Alcotest.(check string)
    "A string in Camel Case should be converted to snake_case" "snake_case"
    (camel_to_snake "SnakeCase")

let test_snake_case_to_snake_id () =
  Alcotest.(check string)
    "A string already in snake_case should stay in snake_case" "snake_case"
    (camel_to_snake "snake_case")

let test_snake_case_to_snake_empty () =
  Alcotest.(check string)
    "An empty string should remain empty after camel to snake case" ""
    (camel_to_snake "")

let test_output_format_parsing_roundtrip_prop =
  QCheck.Test.make ~count:1000 ~name:"parsing an output format roundtrip"
    output_format_arbitrary (fun output_format ->
      let repr = output_format_to_string output_format in
      let parsed_res = arg_to_output_format repr in
      match parsed_res with
      | Ok parsed -> parsed = output_format
      | Error _ -> false)

let test_transformation_kind_parsing_roundtrip_prop =
  QCheck.Test.make ~count:1000 ~name:"parsing a transformation kind roundtrip"
    transformation_kind_arbitrary (fun transformation_kind ->
      let repr = transformation_kind_to_string transformation_kind in
      let parsed_res = arg_to_transformation_kind repr in
      match parsed_res with
      | Ok parsed -> parsed = transformation_kind
      | Error _ -> false)

let test_transformation_steps_parsing_roundtrip_prop =
  QCheck.Test.make ~count:1000
    ~name:"parsing a transformation steps list roundtrip"
    QCheck.(list transformation_kind_arbitrary)
    (fun l ->
      let l_repr = transformation_steps_to_string l in
      let parsed_res = parse_transformation_steps l_repr in
      match parsed_res with
      | Ok parsed -> List.equal ( = ) parsed l
      | Error _ -> false)

let test_camel_to_snake_case_idempotent_prop =
  QCheck.Test.make ~count:1000
    ~name:
      "Applying camel to snake case twice should return the same string as the \
       first"
    QCheck.(string_printable)
    (fun s -> camel_to_snake (camel_to_snake s) = camel_to_snake s)

let test_create_progress_negative_start_fail_prop =
  QCheck.Test.make ~count:1000
    ~name:"Creating a progress struct with a negative current count fail"
    QCheck.(pair int_neg int)
    (fun (neg_start, total) ->
      Result.is_error (create_progress neg_start total))

let test_create_progress_negative_total_fail_prop =
  QCheck.Test.make ~count:1000
    ~name:"Creating a progress struct with a negative total fail"
    QCheck.(pair int int_neg)
    (fun (current, neg_total) ->
      Result.is_error (create_progress current neg_total))

let test_create_progress_total_is_zero_fail_prop =
  QCheck.Test.make ~count:1000
    ~name:"Creating a progress struct with a total of zero fail"
    QCheck.(int_pos)
    (fun current -> Result.is_error (create_progress current 0))

let test_create_progress_correct_range_succeed_prop =
  QCheck.Test.make ~count:1000
    ~name:"Creating a progress struct with a valid range should succeed"
    QCheck.(pair int_pos int_pos)
    (fun (current, total) ->
      QCheck.assume (current <= total);
      Result.is_ok (create_progress current total))

let () =
  let qcheck_tests =
    List.map QCheck_alcotest.to_alcotest
      [
        test_camel_to_snake_case_idempotent_prop;
        test_transformation_steps_parsing_roundtrip_prop;
        test_output_format_parsing_roundtrip_prop;
        test_create_progress_negative_start_fail_prop;
        test_create_progress_negative_total_fail_prop;
        test_create_progress_total_is_zero_fail_prop;
        test_create_progress_correct_range_succeed_prop;
      ]
  in

  Alcotest.run "Cli module tests"
    [
      ("Property tests", qcheck_tests);
      ( "cli tests",
        [
          Alcotest.test_case
            "Check converting a Camel Case string to snake_case" `Quick
            test_camel_to_snake_simple;
          Alcotest.test_case
            "Check converting a snake_case string to snake_case" `Quick
            test_snake_case_to_snake_id;
          Alcotest.test_case "Check converting an empty string to snake case"
            `Quick test_snake_case_to_snake_empty;
        ] );
    ]
