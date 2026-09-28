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

let test_overlapping_comment_delimiters () =
  Alcotest.(check (result (list (pair string point_testable)) error_testable))
    "Overlapping delimiters are not a comment" (Ok []) (get_comments "(*)")

let test_comment_markers_in_string () =
  let source = "Definition x := \"(* ignored *)\".\n(* kept *)" in
  let expected = Ok [ ("(* kept *)", point ~line:1 ~char:0) ] in
  Alcotest.(check (result (list (pair string point_testable)) error_testable))
    "Comment markers in strings should be ignored" expected
    (get_comments source)

let test_parse_try_rewrite_in_star () =
  let repr = "try (rewrite IHn in *)." in
  let comments = get_comments repr in
  let expected = Ok [] in

  Alcotest.(check (result (list (pair string point_testable)) error_testable))
    "No comments should be parsed" expected comments

let test_comment_positions_across_lines () =
  let repr = "x\n(* first *)\ny\n  (* second *)" in
  let by_repr = List.sort (fun (a, _) (b, _) -> String.compare a b) in
  let comments = get_comments repr |> Result.map by_repr in
  let expected =
    Ok
      [
        ("(* first *)", point ~line:1 ~char:0);
        ("(* second *)", point ~line:3 ~char:2);
      ]
  in
  Alcotest.(check (result (list (pair string point_testable)) error_testable))
    "Comments should keep their positions across lines" expected comments

(* let test_parse_nested_comment () = *)
(*   let repr = "(\* (\* abcd *\) *\)" in *)
(*   let comments = get_comments repr in *)

(*   let expected = Ok [ (repr, Code_point.origin) ] in *)

(*   Alcotest.(check (result (list (pair string point_testable)) error_testable)) *)
(*     "A single comment starting at origin should be parsed" expected comments *)

(* let test_parse_malformed_single_star () = *)
(*   let repr = "(\*\)" in *)
(*   let comments = get_comments repr in *)

(*   let expected = Error.string_to_or_error "" in *)

(*   Alcotest.(check (result (list (pair string point_testable)) error_testable)) *)
(*     "No comment should be parsed" expected comments *)

let no_comment_smaller_than_four_characters_prop =
  QCheck.Test.make ~count:1000000
    ~name:"No comment parsable from a string of three characters"
    (QCheck.string_size_of (QCheck.Gen.int_bound 3) QCheck.Gen.char_printable)
    (fun str ->
      match get_comments str with
      | Ok [] -> true
      | Ok (_ :: _) -> false
      | Error _ -> true)

let () =
  let qcheck_tests =
    List.map QCheck_alcotest.to_alcotest
      [ no_comment_smaller_than_four_characters_prop ]
  in

  Alcotest.run "Comment scanner tests"
    [
      ( "Comment parsing",
        [
          test_case "test that a simple single comment is parsed correctly"
            `Quick test_parse_single_simple_comment;
          test_case "test parsing a string with no comments" `Quick
            test_parse_no_comment;
          test_case "test overlapping comment delimiters" `Quick
            test_overlapping_comment_delimiters;
          test_case "test comment markers in strings" `Quick
            test_comment_markers_in_string;
          test_case "test parsing try (rewrite _ in *)" `Quick
            test_parse_try_rewrite_in_star;
          test_case "test comment positions across lines" `Quick
            test_comment_positions_across_lines;
          (* test_case "test parsing nested comments" `Quick *)
          (*   test_parse_nested_comment; *)
          (* test_case "test parsing (\*\)" `Quick test_parse_malformed_single_star; *)
        ]
        @ qcheck_tests );
    ]
