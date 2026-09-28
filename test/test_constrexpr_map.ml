let test_identity_preserves_locations () =
  let reference name start stop =
    let loc = Loc.make_loc (start, stop) in
    CAst.make ~loc
      (Constrexpr.CRef (Libnames.qualid_of_string ~loc name, None))
  in
  let function_ = reference "f" 0 1 in
  let argument = reference "x" 2 3 in
  let term =
    CAst.make ~loc:(Loc.make_loc (0, 3))
      (Constrexpr.CApp (function_, [ (argument, None) ]))
  in
  let mapped = Ditto.Constrexpr_map.constr_expr_map Fun.id term in
  Alcotest.(check bool) "identity map preserves the term" true (mapped = term)

let () =
  Alcotest.run "Constrexpr_map"
    [
      ( "identity",
        [
          Alcotest.test_case "preserves nested source locations" `Quick
            test_identity_preserves_locations;
        ] );
    ]
