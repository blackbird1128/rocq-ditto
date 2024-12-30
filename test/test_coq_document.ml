let test_parsing () =
  Fl_dynload.load_packages [ "coq-lsp.serlib.ltac" ];
  let doc =
    Ditto.Coq_document.doc_of_yojson
      (Yojson.Safe.from_file "fixtures/ex1.v.astdump.json")
  in
  Alcotest.(check int)
    "parsed document isn't of the expected size" 10 (List.length doc.elements)

let tests =
  [
    ( "coq document tests",
      [ Alcotest.test_case "check basic parsing" `Quick test_parsing ] );
  ]

let () = Alcotest.run "coq document test global" tests
