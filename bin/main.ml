(* Basic LSP client using the LSP library in OCaml *)

open Lsp
open Types
open Ditto.Coq_document
open Ditto.Proof
open Ditto.Int_hash
open Ditto.Lsp_client
open Ditto.Request_counter

let read_all file_path =
  (* open_in_bin works correctly on Unix and. Windows *)
  let ch = open_in_bin file_path in
  let s = really_input_string ch (in_channel_length ch) in
  close_in ch;
  s

let create_text_document document_path =
  let text = read_all document_path in
  let uri = Uri.of_path document_path in
  Types.TextDocumentItem.create ~languageId:"coq" ~text ~uri ~version:0

let display_range (x : rangedSpan) : unit = print_endline (show_range x.range)

let () =
  let coq_lsp_in, coq_lsp_out = Unix.open_process "coq-lsp" in
  (* coq_lsp_in is an input channel that get the output of coq_lsp and coq_lsp_out is an output channel to send things to coq_lsp *)
  let request_hashtbl = IntHashtbl.create 50 in
  send_init_request coq_lsp_out;
  let _ = get_response_sync 0 request_hashtbl coq_lsp_in in
  let initialization_notif = Client_notification.Initialized in
  send_json_request coq_lsp_out (serialize_notification initialization_notif);
  let filename = "./example1.v" in

  let document_open_notif =
    Client_notification.TextDocumentDidOpen
      (Types.DidOpenTextDocumentParams.create
         ~textDocument:(create_text_document filename))
  in
  document_open_notif |> serialize_notification |> send_json_request coq_lsp_out;

  let versioned_document =
    Types.VersionedTextDocumentIdentifier.create ~uri:(Uri.of_path filename)
      ~version:0
  in
  let versioned_document_json =
    Types.VersionedTextDocumentIdentifier.yojson_of_t versioned_document
  in
  let id_ast_req = RequestCounter.next () in
  let ast_request =
    Jsonrpc.Request.create
      ~params:(`Assoc [ ("textDocument", versioned_document_json) ])
      ~method_:"coq/getDocument" ~id:(`Int id_ast_req) ()
  in

  send_json_request coq_lsp_out
    (Yojson.Safe.to_string (Jsonrpc.Request.yojson_of_t ast_request));
  print_endline
    (Yojson.Safe.to_string (Jsonrpc.Request.yojson_of_t ast_request));
  let ast_resp = get_response_sync id_ast_req request_hashtbl coq_lsp_in in

  let ast_json_file = open_out "out.json" in
  Yojson.Safe.pretty_to_channel ast_json_file ast_resp;
  let parsed_ast_repr = parse_document ast_resp in

  print_endline (show_completionStatus parsed_ast_repr.completed);
  let coq_ast_doc = lsp_doc_to_coq_doc parsed_ast_repr in

  List.iter
    (fun x ->
      is_ranged_coq_span_tactic x;
      ())
    coq_ast_doc.spans;

  (* let proofs = get_proofs coq_ast_doc in
     let first_tac_start = (List.nth (List.hd proofs).proof_steps 1).range.start in
     let first_tac_position =
       Position.create ~character:first_tac_start.character
         ~line:first_tac_start.line
     in
     let id_tactic_request = RequestCounter.next () in
     let tactic_request =
       Jsonrpc.Request.create
         ~params:
           (`Assoc
             [
               ("textDocument", versioned_document_json);
               ("position", Position.yojson_of_t first_tac_position);
             ])
         ~method_:"proof/goals" ~id:(`Int id_tactic_request) ()
     in
     send_json_request coq_lsp_out
       (Yojson.Safe.to_string (Jsonrpc.Request.yojson_of_t tactic_request));
     print_endline
       (Yojson.Safe.to_string (Jsonrpc.Request.yojson_of_t tactic_request));
     let tactic_resp =
       get_response_sync id_tactic_request request_hashtbl coq_lsp_in
     in
     let ast_json_file = open_out "out1.json" in
     Yojson.Safe.pretty_to_channel ast_json_file tactic_resp; *)

  (* List.iter
       (fun x ->
         if is_ranged_coq_span_proof_start x then
           print_endline ("proof start : " ^ show_range x.range)
         else if is_ranged_coq_span_proof_end x then
           print_endline ("proof end : " ^ show_range x.range))
       coq_ast_doc.spans;
     print_endline
       ("number of proofs: "
       ^ Stdlib.string_of_int (List.length (get_proofs coq_ast_doc))); *)
  shutdown_server coq_lsp_out coq_lsp_in request_hashtbl;
  close_in coq_lsp_in;
  close_out coq_lsp_out
