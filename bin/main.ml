
(* Basic LSP client using the LSP library in OCaml *)

open Lsp.Types 
open Lsp

(* Initialize the client with basic configuration *)
let create_initialize_client_request () = 
  let client_capabilities = ClientCapabilities.create () in
  let init_params = InitializeParams.create 
    ~capabilities: client_capabilities
    ~trace: TraceValues.Verbose () in
  init_params

(* Function to send an initialization request *)
let send_init_request () =
  let param = create_initialize_client_request() in 
  let request = Client_request.Initialize param in
  let int_id : Jsonrpc.Id.t = `Int 1 in
  let jsonrpc_request = Client_request.to_jsonrpc_request request ~id:int_id in
  let jsonrpc_request_json = Jsonrpc.Request.yojson_of_t jsonrpc_request in
  let json_string = Yojson.Safe.to_string jsonrpc_request_json in

  output_string stdout ( "Content-Length:" ^ ( Stdlib.string_of_int (String.length json_string + 2)) ^ "\r\n\r\n" );
  output_string stdout json_string;
  flush stdout;
  (* let request = (Client_request.Initialize param) in  *)
  (* let r = InitializeResult.yojson_of_t request in *)
  (* let json_string = Yojson.Safe.to_string (Client_request.yojson_of_result jsonrpc_request) in *)
  (* (* Assuming a simple communication over stdin/stdout for LSP *) *)
  (* output_string stdout a; *)
(* flush stdout *) 
  ()

(* (* Function to handle incoming messages from the server *)
let handle_message msg =
  match Yojson.Safe.from_string msg with
  | `Assoc [("jsonrpc", `String "2.0"); ("id", _); ("result", result)] ->
      print_endline ("Server response: " ^ Yojson.Safe.to_string result)
  | _ -> print_endline "Unknown message format" *)

(* Main loop for sending and receiving LSP messages *)
(* let rec client_loop () =
  try
    let line = input_line stdin in
    output_string stdout line;
    handle_message line;
    client_loop ()
  with End_of_file ->
    print_endline "End of input";
    exit 0 *)

let () = 
  (* let rc = open_out "log.txt" in *)
  send_init_request ();
  (* client_loop () *)
  let line1 = input_line stdin in output_string stdout line1;
  (*
  let line2 = input_line stdin in 
  let line3 = input_line stdin in 
  output_string rc line1;
  output_string rc line2;
  output_string rc line3;
  close_out rc *)
  ()
  

