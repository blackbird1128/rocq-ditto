open Alcotest
open Ditto

let test_ast_open () =
  let json = Yojson.Safe.from_file "fixtures/ex1.v.ast.json" in
  let doc = Coq_document.parse_document json in
  check string "same string" (List.nth doc.completed.status 0) "Yes"

let () =
  run "Ditto library tests"
    [ ("Ast tests", [ test_case "ast parsing work" `Quick test_ast_open ]) ]
