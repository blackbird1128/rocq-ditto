open Ditto_cli_lib.Env
open Ditto_test_support.Test_support

let env_testable = Alcotest.testable pp equal

let test_of_array_simple () =
  let arr = [| "a=val_a"; "b=val_b" |] in
  let expected = Ok ([ ("a", "val_a"); ("b", "val_b") ] |> of_assoc_list) in

  Alcotest.check
    (Alcotest.result env_testable error_testable)
    "" expected (arr |> of_array)

let test_of_array_empty () =
  let arr = [||] in
  let expected = Ok ([] |> of_assoc_list) in

  Alcotest.check
    (Alcotest.result env_testable error_testable)
    "" expected (arr |> of_array)

let () =
  Alcotest.run "Env module tests"
    [
      ( "env tests",
        [
          Alcotest.test_case "Check converting a simple array to an env" `Quick
            test_of_array_simple;
          Alcotest.test_case "Check converting an empty array to an env" `Quick
            test_of_array_empty;
        ] );
    ]
