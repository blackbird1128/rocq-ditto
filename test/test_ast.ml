open Alcotest
open Ditto

let test_ast_open () =
  let json = Yojson.Safe.from_file "fixtures/ex1.v.ast.json" in
  let doc = Coq_document.parse_document json in
  check string "same string" (List.nth doc.completed.status 0) "Yes"

let test_ast_dump () =
  let json = Yojson.Safe.from_file "fixtures/ex2.v.ast.json" in
  let doc = Coq_document.parse_document json in
  let coq_doc = Coq_document.lsp_doc_to_coq_doc doc in
  let first_line =
    Coq_document.ranged_coq_span_to_string (List.nth coq_doc.spans 2)
  in
  check string "same string" (List.nth doc.completed.status 0) first_line

let () =
  run "Ditto library tests"
    [
      ( "Ast tests",
        [
          (* test_case "ast parsing work" `Quick test_ast_open; *)
          test_case "ast dump work" `Quick test_ast_dump;
        ] );
    ]
