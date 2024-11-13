open Lsp
open Types
open Request_counter
open Int_hash
open Logging

exception Not_Implemented of string

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
