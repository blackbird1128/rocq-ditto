open Ditto

let test_prefix_before_origin_is_empty () =
  Alcotest.(check string)
    "The layout prefix before the origin should be empty" ""
    (Layout.prefix_before Code_point.origin)

let test_prefix_before_newline_count_equal_to_prefix_line =
  QCheck.Test.make ~count:1000
    ~name:
      "The number of newline in the prefix before is equal to the first node \
       line"
    QCheck.(pair int_pos_mid int_pos_mid)
    (fun (line, character) ->
      let p : Code_point.t = { line; character } in
      let prefix = Layout.prefix_before p in
      let newline_count =
        String.fold_left
          (fun count c -> if Char.equal c '\n' then count + 1 else count)
          0 prefix
      in
      newline_count = line)

let test_prefix_before_space_count_equal_to_prefix_char =
  QCheck.Test.make ~count:1000
    ~name:
      "The number of spaces in the prefix before is equal to the first node \
       char"
    QCheck.(pair int_pos_mid int_pos_mid)
    (fun (line, character) ->
      let p : Code_point.t = { line; character } in
      let prefix = Layout.prefix_before p in
      let space_count =
        String.fold_left
          (fun count c -> if Char.equal c ' ' then count + 1 else count)
          0 prefix
      in
      space_count = character)

let test_only_space_and_newline_in_prefix_before =
  QCheck.Test.make ~count:1000
    ~name:"The prefix before is only made of spaces and newlines"
    QCheck.(pair int_pos_mid int_pos_mid)
    (fun (line, character) ->
      let p : Code_point.t = { line; character } in
      let prefix = Layout.prefix_before p in
      String.for_all (fun c -> Char.equal c ' ' || Char.equal c '\n') prefix)

let () =
  let qcheck_tests =
    List.map QCheck_alcotest.to_alcotest
      [
        test_prefix_before_newline_count_equal_to_prefix_line;
        test_prefix_before_space_count_equal_to_prefix_char;
        test_only_space_and_newline_in_prefix_before;
      ]
  in

  Alcotest.run "Layout module tests"
    [
      ("Property tests", qcheck_tests);
      ( "Layout tests",
        [
          Alcotest.test_case "Check that the prefix before the origin is empty"
            `Quick test_prefix_before_origin_is_empty;
        ] );
    ]
