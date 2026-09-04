open Alcotest
open Ditto.Code_range
open Ditto_test_support.Test_support
open Ditto

let test_simple_overlapping () =
  check bool "overlapping simple" true (are_flat_ranges_colliding (2, 5) (4, 6))

let test_no_overlapping () =
  check bool "no overlap" false (are_flat_ranges_colliding (1, 3) (4, 6))

let test_exact_match_collision () =
  check bool "exact match" true (are_flat_ranges_colliding (2, 5) (2, 5))

let test_a_contains_b_collision () =
  check bool "a contains b" true (are_flat_ranges_colliding (2, 10) (4, 5))

let test_b_contains_a_collision () =
  check bool "b contains a" true (are_flat_ranges_colliding (4, 5) (2, 10))

let test_no_overlapping_half_open_glued_prop =
  QCheck.Test.make ~count:1000
    ~name:"half open contiguous ranges (a,b) and (b,c) don't collide"
    QCheck.(triple (int_range 0 10) (int_range 11 20) (int_range 21 30))
    (fun (a, b, c) -> not (are_flat_ranges_colliding (a, b) (b, c)))

let test_flat_ranges_colliding_symmetric_prop =
  QCheck.Test.make ~count:1000 ~name:"are_flat_ranges_colliding is symmetric"
    QCheck.(
      quad (int_range 0 10) (int_range 11 20) (int_range 21 30)
        (int_range 31 40))
    (fun (a, b, c, d) ->
      are_flat_ranges_colliding (a, b) (c, d)
      = are_flat_ranges_colliding (c, d) (a, b))

let test_range_collide_with_itself_prop =
  QCheck.Test.make ~count:1000 ~name:"a range collides with itself"
    QCheck.(
      quad (int_range 0 100) (int_range 0 50) (int_range 101 200)
        (int_range 0 50))
    (fun (a_line, a_char, b_line, b_char) ->
      let a_point = point ~line:a_line ~char:a_char in
      let b_point = point ~line:b_line ~char:b_char in
      let range = range ~start:a_point ~end_:b_point in

      are_colliding range range)

let test_range_contains_itself_prop =
  QCheck.Test.make ~count:1000 ~name:"a range contains itself"
    QCheck.(
      quad (int_range 0 100) (int_range 0 50) (int_range 101 200)
        (int_range 0 50))
    (fun (a_line, a_char, b_line, b_char) ->
      let a_point = point ~line:a_line ~char:a_char in
      let b_point = point ~line:b_line ~char:b_char in
      let range = range ~start:a_point ~end_:b_point in

      range_contains_other ~container:range range)

let test_empty_range_contains_no_other_range_prop =
  QCheck.Test.make ~count:1000 ~name:"an empty range contains no other range"
    QCheck.(
      quad (int_range 0 100) (int_range 0 50) (int_range 101 200)
        (int_range 0 50))
    (fun (a_line, a_char, b_line, b_char) ->
      let empty_range =
        range ~start:Code_point.origin ~end_:Code_point.origin
      in

      let a_point = point ~line:a_line ~char:a_char in
      let b_point = point ~line:b_line ~char:b_char in
      let other_range = range ~start:a_point ~end_:b_point in

      not (range_contains_other ~container:empty_range other_range))

let test_empty_range_collides_with_no_other_range_prop =
  QCheck.Test.make ~count:1000
    ~name:"an empty range collides with no other range"
    QCheck.(
      quad (int_range 0 100) (int_range 0 50) (int_range 101 200)
        (int_range 0 50))
    (fun (a_line, a_char, b_line, b_char) ->
      let empty_range =
        range ~start:Code_point.origin ~end_:Code_point.origin
      in

      let a_point = point ~line:a_line ~char:a_char in
      let b_point = point ~line:b_line ~char:b_char in
      let other_range = range ~start:a_point ~end_:b_point in

      not (are_colliding other_range empty_range))

let test_single_line_ranges_on_different_line_dont_intersect_prop =
  QCheck.Test.make ~count:1000
    ~name:"two single line ranges on different lines don't intersect"
    QCheck.(
      pair
        (triple (int_range 0 100) (int_range 0 50) (int_range 0 50))
        (triple (int_range 101 200) (int_range 0 50) (int_range 0 50)))
    (fun ( (a_line, a_char_start, a_char_offset),
           (b_line, b_char_start, b_char_offset) )
       ->
      let a_start : Code_point.t = point ~line:a_line ~char:a_char_start in
      let a_end : Code_point.t =
        point ~line:a_line ~char:(a_char_start + a_char_offset)
      in

      let a : Code_range.t = range ~start:a_start ~end_:a_end in

      let b_start : Code_point.t = point ~line:b_line ~char:b_char_start in
      let b_end : Code_point.t =
        point ~line:b_line ~char:(b_char_start + b_char_offset)
      in
      let b : Code_range.t = range ~start:b_start ~end_:b_end in

      not (are_colliding a b))

let test_collision_symmetric_prop =
  QCheck.Test.make ~count:1000 ~name:"are_colliding is symmetric"
    QCheck.(
      pair
        (quad (int_range 0 200) (int_range 0 50) (int_range 0 50)
           (int_range 0 50))
        (quad (int_range 0 200) (int_range 0 50) (int_range 0 50)
           (int_range 0 50)))
    (fun ( (a_line, a_char, a_l_offset, a_c_offset),
           (b_line, b_char, b_l_offset, b_c_offset) )
       ->
      let a_start : Code_point.t = point ~line:a_line ~char:a_char in
      let a_end : Code_point.t =
        point ~line:(a_line + a_l_offset) ~char:(a_char + a_c_offset)
      in

      let a : Code_range.t = range ~start:a_start ~end_:a_end in

      let b_start : Code_point.t = point ~line:b_line ~char:b_char in

      let b_end : Code_point.t =
        point ~line:(b_line + b_l_offset) ~char:(b_char + b_c_offset)
      in
      let b = range ~start:b_start ~end_:b_end in

      are_colliding a b = are_colliding b a)

let test_containement_implies_collision_prop =
  QCheck.Test.make ~count:1000 ~name:"contains a b -> are_colliding a b"
    QCheck.(
      pair
        (quad (int_range 0 200) (int_range 0 50) (int_range 0 50)
           (int_range 0 50))
        (quad (int_range 0 200) (int_range 0 50) (int_range 0 50)
           (int_range 0 50)))
    (fun ( (a_line, a_char, a_l_offset, a_c_offset),
           (b_line, b_char, b_l_offset, b_c_offset) )
       ->
      let a_start = point ~line:a_line ~char:a_char in
      let a_end =
        point ~line:(a_line + a_l_offset) ~char:(a_char + a_c_offset)
      in

      let a : Code_range.t = range ~start:a_start ~end_:a_end in

      let b_start = point ~line:b_line ~char:b_char in

      let b_end =
        point ~line:(b_line + b_l_offset) ~char:(b_char + b_c_offset)
      in
      let b = range ~start:b_start ~end_:b_end in

      if range_contains_other ~container:a b then are_colliding a b else true)

let test_no_collision_glued_prop =
  QCheck.Test.make ~count:1000 ~name:"ranges [a,b) and [b,c) don't collides"
    QCheck.(
      pair
        (quad (int_range 0 200) (int_range 0 50) (int_range 0 50)
           (int_range 0 50))
        (pair (int_range 0 50) (int_range 0 50)))
    (fun ((a_line, a_char, a_l_offset, a_c_offset), (c_l_offset, c_c_offset)) ->
      let a = point ~line:a_line ~char:a_char in
      let b = point ~line:(a_line + a_l_offset) ~char:(a_char + a_c_offset) in
      let c =
        point ~line:(b.line + c_l_offset) ~char:(b.character + c_c_offset)
      in

      let first_range : Code_range.t = range ~start:a ~end_:b in
      let second_range : Code_range.t = range ~start:b ~end_:c in

      not (are_colliding first_range second_range))

let test_compare_zero_equivalent_to_equality =
  QCheck.Test.make ~count:1000 ~name:"compare a b = 0 <-> equal a b"
    QCheck.(
      pair
        (quad (int_range 0 200) (int_range 0 50) (int_range 0 50)
           (int_range 0 50))
        (quad (int_range 0 200) (int_range 0 50) (int_range 0 50)
           (int_range 0 50)))
    (fun ( (a_line, a_char, a_l_offset, a_c_offset),
           (b_line, b_char, b_l_offset, b_c_offset) )
       ->
      let a_start = point ~line:a_line ~char:a_char in

      let a_end =
        point ~line:(a_line + a_l_offset) ~char:(a_char + a_c_offset)
      in
      let a : Code_range.t = range ~start:a_start ~end_:a_end in

      let b_start = point ~line:b_line ~char:b_char in

      let b_end =
        point ~line:(b_line + b_l_offset) ~char:(b_char + b_c_offset)
      in
      let b = range ~start:b_start ~end_:b_end in

      if compare a b = 0 then equal a b else not (equal a b))

let test_to_yojson_simple () =
  let start = point ~line:0 ~char:10 in
  let end_ = point ~line:5 ~char:12 in
  let range = range ~start ~end_ in
  let json_repr = to_yojson range in
  let expected : Yojson.Safe.t =
    `Assoc
      [
        ("start", `Assoc [ ("line", `Int 0); ("character", `Int 10) ]);
        ("end_", `Assoc [ ("line", `Int 5); ("character", `Int 12) ]);
      ]
  in

  Alcotest.check yojson_testable
    "the Json representation should be fixed to this representation" expected
    json_repr

let test_of_yojson_simple () =
  let json_repr =
    `Assoc
      [
        ("start", `Assoc [ ("line", `Int 0); ("character", `Int 10) ]);
        ("end_", `Assoc [ ("line", `Int 5); ("character", `Int 12) ]);
      ]
  in

  let parsed =
    of_yojson json_repr
    |> expect_ok ~context:"expecting parsing to succeed"
         ~pp_error:Format.pp_print_string
  in

  let start = point ~line:0 ~char:10 in
  let end_ = point ~line:5 ~char:12 in

  let expected = range ~start ~end_ in

  Alcotest.check range_testable "a range should be parsed from this Json shape"
    expected parsed

let test_roundtrip_parsing_json_prop =
  QCheck.Test.make ~count:1000
    ~name:"Json parsing and serialization is round trip"
    QCheck.(pair (pair int_pos_mid int_pos_mid) (pair int_pos_mid int_pos_mid))
    (fun ((start_line, start_char), (end_line_offset, end_char_offset)) ->
      let start = point ~line:start_line ~char:start_char in
      let end_ =
        point
          ~line:(start_line + end_line_offset)
          ~char:(start_char + end_char_offset)
      in
      let range = range ~start ~end_ in

      let json_repr = to_yojson range in
      let of_json_repr_res = of_yojson json_repr in
      match of_json_repr_res with
      | Ok parsed_range -> equal parsed_range range
      | Error _ -> false)

let test_to_sexp_simple () =
  let start = point ~line:0 ~char:10 in
  let end_ = point ~line:5 ~char:12 in
  let range = range ~start ~end_ in
  let sexp_repr = sexp_of_t range in

  let expected : Sexplib.Sexp.t =
    List
      [
        List [ Atom "start"; Code_point.sexp_of_t start ];
        List [ Atom "end_"; Code_point.sexp_of_t end_ ];
      ]
  in

  Alcotest.check sexp_testable
    "the Sexp representation should be fixed to this representation" expected
    sexp_repr

let test_of_sexp_simple () =
  let sexp_repr : Sexplib.Sexp.t =
    List
      [
        List
          [
            Atom "start";
            List
              [
                List [ Atom "line"; Atom "0" ];
                List [ Atom "character"; Atom "10" ];
              ];
          ];
        List
          [
            Atom "end_";
            List
              [
                List [ Atom "line"; Atom "5" ];
                List [ Atom "character"; Atom "12" ];
              ];
          ];
      ]
  in

  let parsed = t_of_sexp sexp_repr in
  let start = point ~line:0 ~char:10 in
  let end_ = point ~line:5 ~char:12 in
  let expected = range ~start ~end_ in

  Alcotest.check range_testable "a range should be parsed from this S-exp shape"
    expected parsed

let test_roundtrip_parsing_sexp_prop =
  QCheck.Test.make ~count:1000
    ~name:"S-exp parsing and serialization is round tripping"
    QCheck.(pair (pair int_pos_mid int_pos_mid) (pair int_pos_mid int_pos_mid))
    (fun ((start_line, start_char), (end_line_offset, end_char_offset)) ->
      let start = point ~line:start_line ~char:start_char in
      let end_ =
        point
          ~line:(start_line + end_line_offset)
          ~char:(start_char + end_char_offset)
      in
      let range = range ~start ~end_ in

      let sexp_repr = sexp_of_t range in
      let of_sexp_repr = t_of_sexp sexp_repr in

      equal range of_sexp_repr)

let () =
  let qcheck_tests_parsing_json =
    List.map QCheck_alcotest.to_alcotest [ test_roundtrip_parsing_json_prop ]
  in

  let qcheck_tests_parsing_sexp =
    List.map QCheck_alcotest.to_alcotest [ test_roundtrip_parsing_sexp_prop ]
  in

  let qcheck_tests =
    List.map QCheck_alcotest.to_alcotest
      [
        test_no_overlapping_half_open_glued_prop;
        test_flat_ranges_colliding_symmetric_prop;
        test_range_contains_itself_prop;
        test_empty_range_contains_no_other_range_prop;
        test_empty_range_collides_with_no_other_range_prop;
        test_containement_implies_collision_prop;
        test_no_collision_glued_prop;
        test_range_collide_with_itself_prop;
        test_collision_symmetric_prop;
        test_single_line_ranges_on_different_line_dont_intersect_prop;
        test_compare_zero_equivalent_to_equality;
      ]
  in

  run "Range module tests"
    [
      ("Properties", qcheck_tests);
      ( "Json representation",
        [
          test_case
            "test that a range is serialized to the expected Json \
             representation"
            `Quick test_to_yojson_simple;
          test_case
            "test that a range can be parsed from the expected Json \
             representation"
            `Quick test_of_yojson_simple;
        ]
        @ qcheck_tests_parsing_json );
      ( "S-exp representation",
        [
          test_case
            "test that a range is serialized to the expected S-exp \
             representation"
            `Quick test_to_sexp_simple;
          test_case
            "test that a range can be parsed from the expected S-exp \
             representation"
            `Quick test_of_sexp_simple;
        ]
        @ qcheck_tests_parsing_sexp );
      ( "Collisions",
        [
          test_case "test two ranges overlapping" `Quick test_simple_overlapping;
          test_case "test two ranges not overlapping" `Quick test_no_overlapping;
          test_case "test two ranges exactly overlapping" `Quick
            test_exact_match_collision;
          test_case "test two ranges where a contains b" `Quick
            test_a_contains_b_collision;
          test_case "test two ranges where b contains a" `Quick
            test_b_contains_a_collision;
        ] );
    ]
