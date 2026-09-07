open Ditto_cli_lib.Plugin_configuration

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
