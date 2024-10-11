
(* Basic LSP client using the LSP library in OCaml *)

open Lsp.Types 
open Lsp

let log_to_file filename line =
  let oc = open_out_gen [Open_append; Open_creat] 0o666 filename in
  output_string oc (line ^ "\n");
  close_out oc

(* Initialize the client with basic configuration *)
let create_initialize_client_request () = 
  let client_capabilities = ClientCapabilities.create () in
  let init_params = InitializeParams.create 
    ~capabilities: client_capabilities
    ~trace: TraceValues.Off
    ~processId: (-1)
    () in
  init_params

(* Function to send an initialization request *)
let send_init_request input_channel =
  let param = create_initialize_client_request() in 
  let request = Client_request.Initialize param in
  let int_id : Jsonrpc.Id.t = `Int 1 in
  let jsonrpc_request = Client_request.to_jsonrpc_request request ~id:int_id in
  let jsonrpc_request_json = Jsonrpc.Request.yojson_of_t jsonrpc_request in
  let json_string = Yojson.Safe.to_string jsonrpc_request_json in
  output_string input_channel (Header.to_string (Header.create ~content_length:(String.length json_string) ()));
  output_string input_channel json_string;
  flush input_channel;

  ()

let handle_server_notification server_notification =
    match server_notification with
      | Server_notification.PublishDiagnostics _ -> ()
      | Server_notification.ShowMessage _ -> ()
      | Server_notification.LogMessage _ -> ()
      | Server_notification.LogTrace _ -> ()
      | Server_notification.TelemetryNotification _ -> ()
      | Server_notification.CancelRequest _ -> ()
      | Server_notification.WorkDoneProgress _ -> ()
      | Server_notification.UnknownNotification _ -> ()

  (*Function to handle incoming messages from the server *)
let handle_message msg =
    match Yojson.Safe.from_string msg with
  | `Assoc [("jsonrpc", `String "2.0"); ("result", result)] ->
          output_string stderr ("Server response: " ^ Yojson.Safe.to_string result);
          flush stderr
  | `Assoc [("jsonrpc", `String "2.0");("method", `String method_called);("params", params)] ->
          print_endline method_called;
          let structured_params = Jsonrpc.Structured.t_of_yojson params in
          let notification = Jsonrpc.Notification.create ~params:structured_params ~method_:method_called () in
          let server_notification_result = Lsp.Server_notification.of_jsonrpc notification in
          if not (Result.is_ok server_notification_result) then
              raise (Invalid_argument "server notification parsing failed")
          else
              let server_notification = ( Result.get_ok server_notification_result ) in
              handle_server_notification server_notification
  | _ -> ()

  

let extract_content_length header =
  let re = Str.regexp "Content-Length: \\([0-9]+\\)" in
  if Str.string_match re header 0 then
    (int_of_string (Str.matched_group 1 header) + 2) (* handle \r\n with +2 *)
  else
    failwith "Content-Length not found"

(* Main loop for sending and receiving LSP messages *)
let rec client_loop input_chan () =
  try
    let header = input_line input_chan in
    let content_length = extract_content_length header in
    let json_string = String.trim (Stdlib.really_input_string input_chan content_length) in

    log_to_file "log.txt" json_string;
    print_endline json_string;
    handle_message json_string;
    client_loop input_chan ()
  with End_of_file ->
    print_endline "End of input";
    exit 0

let () = 
  let  (coq_lsp_out,coq_lsp_in) = Unix.open_process "coq-lsp" in
  send_init_request coq_lsp_in;
  client_loop coq_lsp_out ()

(* what the difference between server notification and server request ? *)
