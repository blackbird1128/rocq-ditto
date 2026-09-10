open Alcotest
open Ditto.Code_point
open Ditto_test_support.Test_support

(* ok, this is silly, but at least we can in the future define our own function without breaking something unrelated *)
let test_to_yojson_simple () =
  let x = point ~line:0 ~char:10 in
  let json_repr = to_yojson x in
  let expected : Yojson.Safe.t =
    `Assoc [ ("line", `Int 0); ("character", `Int 10) ]
  in
  Alcotest.check yojson_testable
    "the Json representation should be fixed to this representation" expected
    json_repr

let test_of_yojson_simple () =
  let json_repr = `Assoc [ ("line", `Int 0); ("character", `Int 10) ] in

  let parsed =
    of_yojson json_repr
    |> expect_ok ~context:"expecting parsing to succeed"
         ~pp_error:Format.pp_print_string
  in

  let expected = point ~line:0 ~char:10 in

  Alcotest.check point_testable "a point should be parsed from this Json shape"
    expected parsed

let test_of_yojson_reverse_order () =
  let json_repr = `Assoc [ ("character", `Int 10); ("line", `Int 0) ] in

  let parsed =
    of_yojson json_repr
    |> expect_ok ~context:"expecting parsing to succeed"
         ~pp_error:Format.pp_print_string
  in

  let expected = point ~line:0 ~char:10 in

  Alcotest.check point_testable "a point should be parsed from this Json shape"
    expected parsed

let test_to_sexp_simple () =
  let x = point ~line:0 ~char:10 in
  let sexp_repr = sexp_of_t x in
  let expected : Sexplib.Sexp.t =
    List
      [ List [ Atom "line"; Atom "0" ]; List [ Atom "character"; Atom "10" ] ]
  in

  Alcotest.check sexp_testable
    "the Sexp representation should be fixed to this representation" expected
    sexp_repr

let test_of_sexp_simple () =
  let sexp_repr : Sexplib.Sexp.t =
    List
      [ List [ Atom "line"; Atom "0" ]; List [ Atom "character"; Atom "10" ] ]
  in

  let parsed = of_sexp sexp_repr in
  let expected = make 0 10 in

  Alcotest.check
    (result point_testable error_testable)
    "a point should be parsed from this S-exp shape" expected parsed

let test_roundtrip_parsing_json_prop =
  QCheck.Test.make ~count:1000
    ~name:"Json parsing and serialization is round tripping"
    QCheck.(pair int_pos int_pos)
    (fun (line, char) ->
      let point =
        make line char
        |> expect_result_ok
             ~context:"creating a point from positive coordinates"
      in
      let json_repr = to_yojson point in
      let of_json_repr_res = of_yojson json_repr in
      match of_json_repr_res with
      | Ok parsed_point -> equal parsed_point point
      | Error _ -> false)

let test_roundtrip_parsing_sexp_prop =
  QCheck.Test.make ~count:1000
    ~name:"S-exp parsing and serialization is round tripping"
    QCheck.(pair int_pos int_pos)
    (fun (line, char) ->
      let point =
        make line char
        |> expect_result_ok
             ~context:"creating a point from positive coordinates"
      in

      let sexp_repr = sexp_of_t point in
      let of_sexp_repr = of_sexp sexp_repr in
      match of_sexp_repr with
      | Ok of_sexp -> equal of_sexp point
      | Error _ -> false)

let test_advance_by_text_simple_no_newline () =
  let text = "aaaa" in
  let start_point = origin in

  let expected = point ~line:0 ~char:4 in

  check point_testable "the starting point should be moved by 4 chars" expected
    (advance_by_text start_point text)

let test_advance_by_text_simple_one_newline () =
  let text = "aaaa\naa" in
  let start_point = origin in

  let expected = point ~line:1 ~char:2 in

  check point_testable "the point should advance to the expected point" expected
    (advance_by_text start_point text)

let test_advance_by_empty_string_is_identity_prop =
  QCheck.Test.make ~count:1000
    ~name:
      "Advancing a point by an empty string should leave the point at the \
       start position"
    QCheck.(pair int_pos int_pos)
    (fun (line, char) ->
      let point = point ~line ~char in

      let moved = advance_by_text point "" in
      equal point moved)

let test_advance_by_number_of_newline_in_text_prop =
  QCheck.Test.make ~count:1000
    ~name:
      "Advancing a point by a string should increase the line count by the \
       number of newlines (\n\
       )"
    QCheck.(pair (pair int_pos int_pos) string_printable)
    (fun ((line, char), text) ->
      let start_point = point ~line ~char in

      let number_newline =
        String.fold_left
          (fun count char -> if char = '\n' then count + 1 else count)
          0 text
      in
      let expected =
        shift ~lines:number_newline ~chars:0 start_point
        |> expect_result_ok ~context:"shift by a positive number"
      in

      let moved = advance_by_text start_point text in

      expected.line = moved.line)

let test_advance_without_newline_only_move_char_prop =
  QCheck.Test.make ~count:1000
    ~name:
      "Advancing a point by a string without newlines should only move the \
       number of chars"
    QCheck.(pair (pair int_pos int_pos) string_printable)
    (fun ((line, char), text) ->
      QCheck.assume (not (String.exists (fun c -> c = '\n') text));
      let start_point = point ~line ~char in

      let moved = advance_by_text start_point text in
      start_point.line = moved.line)

let () =
  let qcheck_tests_parsing_json =
    List.map QCheck_alcotest.to_alcotest [ test_roundtrip_parsing_json_prop ]
  in

  let qcheck_tests_parsing_sexp =
    List.map QCheck_alcotest.to_alcotest [ test_roundtrip_parsing_sexp_prop ]
  in

  let qcheck_point_functions_property_tests =
    List.map QCheck_alcotest.to_alcotest
      [
        test_advance_by_empty_string_is_identity_prop;
        test_advance_by_number_of_newline_in_text_prop;
        test_advance_without_newline_only_move_char_prop;
      ]
  in

  run "Point module tests"
    [
      ( "Json representation",
        [
          test_case
            "test that a point is serialized to the expected Json \
             representation"
            `Quick test_to_yojson_simple;
          test_case
            "test that a point can be parsed from the expected Json \
             representation"
            `Quick test_of_yojson_simple;
          test_case
            "test that a point can be parsed from the expected Json fields in \
             the reverse order"
            `Quick test_of_yojson_reverse_order;
        ]
        @ qcheck_tests_parsing_json );
      ( "S-exp representation",
        [
          test_case
            "test that a point is serialized to the expected S-exp \
             representation"
            `Quick test_to_sexp_simple;
          test_case
            "test that a point can be parsed from the expected S-exp \
             representation"
            `Quick test_of_sexp_simple;
        ]
        @ qcheck_tests_parsing_sexp );
      ( "Point functions",
        [
          test_case "test advancing a point by a string of four chars" `Quick
            test_advance_by_text_simple_no_newline;
          test_case
            "test advancing a point by a string with a single newline in the \
             middle"
            `Quick test_advance_by_text_simple_one_newline;
        ]
        @ qcheck_point_functions_property_tests );
    ]
