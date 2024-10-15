
(* Basic LSP client using the LSP library in OCaml *)
(* Input channel: where we wend our inputs  *)
(* output channel: where we get coq_lsp output *)


open Lsp.Types 
open Lsp


module RequestCounter = struct
  (* Mutable state *)
  let counter = ref 0

  (* Function to get the current value and increment *)
  let next () =
    let current = !counter in
    counter := !counter + 1;
    current
end

module IntHash =
    struct 
        type t = int
        let equal i j = i=j
        let hash i = i land max_int
    end

module IntHashtbl = Hashtbl.Make(IntHash)

exception Not_Implemented of string

(**   *)
let log_to_file filename line =
  let oc = open_out_gen [Open_append; Open_creat] 0o666 filename in
  output_string oc (line ^ "\n");
  close_out oc

let serialize_notification notification =
  let json_rpc  = Client_notification.to_jsonrpc notification in
  Yojson.Safe.to_string (Jsonrpc.Notification.yojson_of_t json_rpc)

let serialize_request request id =
  Client_request.to_jsonrpc_request request ~id:id  |>
  Jsonrpc.Request.yojson_of_t |>
  Yojson.Safe.to_string

let send_json_request output_channel request =
  output_string output_channel (Header.to_string (Header.create ~content_length:(String.length request) ()));
  output_string output_channel request;
  flush output_channel

(* Function to send an initialization request *)
let send_init_request output_channel =
  let init_params = InitializeParams.create 
    ~capabilities: ( ClientCapabilities.create ())
    ~trace: TraceValues.Off
    ~processId: (-1)
    () in
  let request = Client_request.Initialize init_params in
  let int_id : Jsonrpc.Id.t = `Int (RequestCounter.next ()) in
  let json_string = serialize_request request int_id in
  send_json_request output_channel json_string

let handle_server_notification server_notification =
    match server_notification with
      | Server_notification.PublishDiagnostics _ -> raise (Not_Implemented "Publish Diagnostic handling not implemented")
      | Server_notification.ShowMessage notif -> print_endline notif.message
      | Server_notification.LogMessage notif -> log_to_file "logs.txt" notif.message 
      | Server_notification.LogTrace _ -> raise (Not_Implemented "Log trace handling not implemented")
      | Server_notification.TelemetryNotification _ -> raise (Not_Implemented "Telemetry Notification handling not implemented")
      | Server_notification.CancelRequest _ -> raise (Not_Implemented "Cancel Request handling not implemented")
      | Server_notification.WorkDoneProgress _ -> raise (Not_Implemented "Work Done Progress handling not implemented")
      | Server_notification.UnknownNotification notif -> print_endline (notif.method_)

  (*Function to handle incoming messages from the server *)
let handle_message msg request_hashtbl =
    match Yojson.Safe.from_string msg with
  | `Assoc [("jsonrpc", `String "2.0");("id", `Int id) ; ("result", result)] ->
          IntHashtbl.add request_hashtbl id result;
          IntHashtbl.iter (fun x y -> Printf.printf "%d -> %s\n" x (Yojson.Safe.to_string y)) request_hashtbl;
          print_newline ();
  | `Assoc [("jsonrpc", `String "2.0");("method", `String method_called);("params", params)] ->
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

let receive_message input_chan =
    let header = input_line input_chan in
    let content_length = extract_content_length header in
    String.trim (Stdlib.really_input_string input_chan content_length)

let rec get_response_sync id request_hashtbl input_chan =
    if IntHashtbl.mem request_hashtbl id then
        IntHashtbl.find request_hashtbl id 
    else
       let json_msg =  receive_message input_chan in
       handle_message json_msg request_hashtbl;
       get_response_sync id request_hashtbl input_chan

let shutdown_server output_channel input_channel request_hashtbl =
    let request = Client_request.Shutdown in
    let id = RequestCounter.next() in
    let rpc_id : Jsonrpc.Id.t = `Int id in
    let json_string = serialize_request request rpc_id in
    send_json_request output_channel json_string;
    let _ = get_response_sync id request_hashtbl input_channel in
    let exit_notification = Client_notification.Exit in
    exit_notification |> serialize_notification |> send_json_request output_channel



let () = 
  let  (coq_lsp_in,coq_lsp_out) = Unix.open_process "coq-lsp" in (* coq_lsp_in is an input channel that get the output of coq_lsp and coq_lsp_out is an output channel to send things to coq_lsp *)
  let request_hashtbl = IntHashtbl.create 50 in
  send_init_request coq_lsp_out;
  let _ = get_response_sync 0 request_hashtbl coq_lsp_in in
  let initialization_notif = Client_notification.Initialized in
  send_json_request coq_lsp_out (serialize_notification initialization_notif);
  shutdown_server coq_lsp_out coq_lsp_in request_hashtbl;
  close_in coq_lsp_in;
  close_out coq_lsp_out
  (* client_loop coq_lsp_out () *)

(* what the difference between server notification and server request ? *)
