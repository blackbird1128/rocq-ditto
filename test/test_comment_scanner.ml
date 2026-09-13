open Ditto.Comment_scanner
open Ditto
open Ditto_test_support.Test_support
open Alcotest

let test_parse_single_simple_comment () =
  let repr = "(* hello world *)" in
  let comments = get_comments repr in
  let expected = Ok [ ("(* hello world *)", Code_point.origin) ] in

  Alcotest.(check (result (list (pair string point_testable)) error_testable))
    "A single comment starting at origin should be parsed" expected comments

let test_parse_no_comment () =
  let repr = "abcde" in
  let comments = get_comments repr in
  let expected = Ok [] in

  Alcotest.(check (result (list (pair string point_testable)) error_testable))
    "No comments should be parsed" expected comments

let test_parse_try_rewrite_in_star () =
  let repr = "try (rewrite IHn in *)." in
  let comments = get_comments repr in
  let expected = Ok [] in

  Alcotest.(check (result (list (pair string point_testable)) error_testable))
    "No comments should be parsed" expected comments

let test_parse_nested_comment () =
  let repr = "(* (* abcd *) *)" in
  let comments = get_comments repr in

  let expected = Ok [ (repr, Code_point.origin) ] in

  Alcotest.(check (result (list (pair string point_testable)) error_testable))
    "A single comment starting at origin should be parsed" expected comments

let test_parse_malformed_single_star () =
  let repr = "(*)" in
  let comments = get_comments repr in

  let expected = Error.string_to_or_error "" in

  Alcotest.(check (result (list (pair string point_testable)) error_testable))
    "No comment should be parsed" expected comments

let () =
  Alcotest.run "Comment scanner tests"
    [
      ( "Comment parsing",
        [
          test_case "test that a simple single comment is parsed correctly"
            `Quick test_parse_single_simple_comment;
          test_case "test parsing a string with no comments" `Quick
            test_parse_no_comment;
          test_case "test parsing try (rewrite _ in *)" `Quick
            test_parse_try_rewrite_in_star;
          test_case "test parsing nested comments" `Quick
            test_parse_nested_comment;
          test_case "test parsing (*)" `Quick test_parse_malformed_single_star;
        ] );
    ]
