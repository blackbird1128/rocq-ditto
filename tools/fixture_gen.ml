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

let () =
  if Array.length Sys.argv <> 2 then
    Printf.eprintf "Usage: %s <source_file>\n" Sys.argv.(0)
  else
    let filename = Sys.argv.(1) in

    let coq_lsp_in, coq_lsp_out = Unix.open_process "coq-lsp" in
    (* coq_lsp_in is an input channel that get the output of coq_lsp and coq_lsp_out is an output channel to send things to coq_lsp *)
    let request_hashtbl = IntHashtbl.create 50 in
    send_init_request coq_lsp_out;
    let _ = get_response_sync 0 request_hashtbl coq_lsp_in in

    let initialization_notif = Client_notification.Initialized in
    send_json_request coq_lsp_out (serialize_notification initialization_notif);

    let document_open_notif =
      Client_notification.TextDocumentDidOpen
        (Types.DidOpenTextDocumentParams.create
           ~textDocument:(create_text_document filename))
    in
    document_open_notif |> serialize_notification
    |> send_json_request coq_lsp_out;

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

    let ast_resp = get_response_sync id_ast_req request_hashtbl coq_lsp_in in

    let ast_json_file = open_out (filename ^ ".ast.json") in
    Yojson.Safe.pretty_to_channel ast_json_file ast_resp;

    shutdown_server coq_lsp_out coq_lsp_in request_hashtbl;
    close_in coq_lsp_in;
    close_out coq_lsp_out
