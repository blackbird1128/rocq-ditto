(* Basic LSP client using the LSP library in OCaml *)

open Lsp
open Ditto.CoqDocument

module RequestCounter = struct
  (* Mutable state *)
  let counter = ref 0

  (* Function to get the current value and increment *)
  let next () =
    let current = !counter in
    counter := !counter + 1;
    current
end

module IntHash = struct
  type t = int

  let equal i j = i = j
  let hash i = i land max_int
end

module IntHashtbl = Hashtbl.Make (IntHash)

exception Not_Implemented of string

(** log a line to a file *)
let log_to_file filename line =
  let oc = open_out_gen [ Open_append; Open_creat ] 0o666 filename in
  output_string oc (line ^ "\n");
  close_out oc

(** turn a Lsp.Client_notification into a string *)
let serialize_notification notification =
  let json_rpc = Client_notification.to_jsonrpc notification in
  Yojson.Safe.to_string (Jsonrpc.Notification.yojson_of_t json_rpc)

(** turn a Lsp.Client_request into a string *)
let serialize_request request id =
  Client_request.to_jsonrpc_request request ~id
  |> Jsonrpc.Request.yojson_of_t |> Yojson.Safe.to_string

(** Send the request to coq-lsp with the appropriate header *)
let send_json_request output_channel request =
  output_string output_channel
    (Header.to_string
       (Header.create ~content_length:(String.length request) ()));
  output_string output_channel request;
  flush output_channel

(* Function to send an initialization request *)
let send_init_request output_channel =
  let init_params =
    Types.InitializeParams.create
      ~capabilities:(Types.ClientCapabilities.create ())
      ~trace:Types.TraceValues.Off ~processId:(-1)
      ~workspaceFolders:
        (Some
           [ Types.WorkspaceFolder.create ~name:"test" ~uri:(Uri.of_path ".") ])
      ()
  in
  let request = Client_request.Initialize init_params in
  let int_id : Jsonrpc.Id.t = `Int (RequestCounter.next ()) in
  let json_string = serialize_request request int_id in
  send_json_request output_channel json_string

(** treat server notifications (mostly just log for now) *)
let handle_server_notification server_notification =
  match server_notification with
  | Server_notification.PublishDiagnostics diagnostics_notif ->
      print_endline
        (Yojson.Safe.to_string
           (Types.PublishDiagnosticsParams.yojson_of_t diagnostics_notif))
  | Server_notification.ShowMessage notif -> print_endline notif.message
  | Server_notification.LogMessage notif -> log_to_file "logs.txt" notif.message
  | Server_notification.LogTrace notif -> log_to_file "trace.txt" notif.message
  | Server_notification.TelemetryNotification _ ->
      raise (Not_Implemented "Telemetry Notification handling not implemented")
  | Server_notification.CancelRequest _ ->
      raise (Not_Implemented "Cancel Request handling not implemented")
  | Server_notification.WorkDoneProgress _ ->
      raise (Not_Implemented "Work Done Progress handling not implemented")
  | Server_notification.UnknownNotification notif ->
      print_endline notif.method_;
      if Option.has_some notif.params then
        print_endline
          (Yojson.Safe.to_string
             (Jsonrpc.Structured.yojson_of_t (Option.get notif.params)))

(*Function to handle incoming messages from the server *)
let handle_message msg request_hashtbl =
  match Yojson.Safe.from_string msg with
  | `Assoc [ ("jsonrpc", `String "2.0"); ("id", `Int id); ("result", result) ]
    ->
      IntHashtbl.add request_hashtbl id result;
      print_newline ()
  | `Assoc
      [
        ("jsonrpc", `String "2.0");
        ("method", `String method_called);
        ("params", params);
      ] ->
      let structured_params = Jsonrpc.Structured.t_of_yojson params in
      let notification =
        Jsonrpc.Notification.create ~params:structured_params
          ~method_:method_called ()
      in
      let server_notification_result =
        Server_notification.of_jsonrpc notification
      in
      if not (Result.is_ok server_notification_result) then
        raise (Invalid_argument "server notification parsing failed")
      else
        let server_notification = Result.get_ok server_notification_result in
        handle_server_notification server_notification
  | _ -> ()

(* extract the content length of a received message *)
let extract_content_length header =
  let open Re.Pcre in
  let re = Re.Pcre.regexp "Content-Length: ([0-9]+)" in
  match Re.exec_opt re header with
  | Some group ->
      int_of_string (Re.Group.get group 1) + 2 (* handle \r\n with +2 *)
  | None -> failwith "Content-Length not found"

(* parse one incoming message from the server *)
let receive_message input_chan =
  let header = input_line input_chan in
  let content_length = extract_content_length header in
  String.trim (Stdlib.really_input_string input_chan content_length)

(* get a response to the request with the id [id] blocking*)
let rec get_response_sync id request_hashtbl input_chan =
  if IntHashtbl.mem request_hashtbl id then IntHashtbl.find request_hashtbl id
  else
    let json_msg = receive_message input_chan in
    handle_message json_msg request_hashtbl;
    get_response_sync id request_hashtbl input_chan

(** shutdown the lsp server*)
let shutdown_server output_channel input_channel request_hashtbl =
  let request = Client_request.Shutdown in
  let id = RequestCounter.next () in
  let rpc_id : Jsonrpc.Id.t = `Int id in
  let json_string = serialize_request request rpc_id in
  send_json_request output_channel json_string;
  let _ = get_response_sync id request_hashtbl input_channel in
  let exit_notification = Client_notification.Exit in
  exit_notification |> serialize_notification
  |> send_json_request output_channel

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

let is_ranged_coq_span_proof_start (x : rangedCoqSpan) : bool =
  if Option.has_some x.span then
    let x_span = Option.get x.span in
    match x_span.CAst.v.expr with
    | VernacSynterp synterp_expr -> false
    | VernacSynPure expr -> (
        match expr with
        | Vernacexpr.VernacStartTheoremProof _ -> true
        | _ -> false)
  else false

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
  let x =
    List.map (fun x -> is_ranged_coq_span_proof_start x) coq_ast_doc.spans
  in
  List.iter (fun w -> print_string (if w then "START PROOF\n" else "")) x;
  shutdown_server coq_lsp_out coq_lsp_in request_hashtbl;
  close_in coq_lsp_in;
  close_out coq_lsp_out
