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

  let expected =
    make 0 10 |> expect_result_ok ~context:"creating a simple expected point"
  in

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

let () =
  let qcheck_tests_parsing_json =
    List.map QCheck_alcotest.to_alcotest [ test_roundtrip_parsing_json_prop ]
  in

  let qcheck_tests_parsing_sexp =
    List.map QCheck_alcotest.to_alcotest [ test_roundtrip_parsing_sexp_prop ]
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
    ]
