open Alcotest
open Ditto.Code_range

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

let () =
  let qcheck_tests =
    List.map QCheck_alcotest.to_alcotest
      [
        test_no_overlapping_half_open_glued_prop;
        test_flat_ranges_colliding_symmetric_prop;
      ]
  in

  run "Range utils"
    [
      ("Properties", qcheck_tests);
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
