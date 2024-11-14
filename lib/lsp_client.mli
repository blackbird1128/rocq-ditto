open Int_hash
(** LSP Client Module Interface *)

exception Not_Implemented of string

val serialize_notification : Lsp.Client_notification.t -> string
(** Serialize a [Lsp.Client_notification] into a string *)

val serialize_request : 'a Lsp.Client_request.t -> Jsonrpc.Id.t -> string

(** Serialize a [Lsp.Client_request] into a string, given its [id] *)

val send_json_request : out_channel -> string -> unit
(** Send a JSON-RPC request string to the Coq-LSP server over the specified output channel *)

val send_init_request : out_channel -> unit
(** Send an initialization request to the LSP server *)

val handle_server_notification : Lsp.Server_notification.t -> unit
(** Handle incoming LSP server notifications *)

val handle_message : string -> Yojson.Safe.t IntHashtbl.t -> unit
(** Handle an incoming server message and update the request hash table *)

val extract_content_length : string -> int
(** Extract the content length from the HTTP-style header of a received message *)

val receive_message : in_channel -> string
(** Receive and parse one incoming message from the server *)

val get_response_sync :
  int -> Yojson.Safe.t IntHashtbl.t -> in_channel -> Yojson.Safe.t
(** Get a response synchronously for a request with the given [id], blocking if necessary *)

val shutdown_server :
  out_channel -> in_channel -> Yojson.Safe.t IntHashtbl.t -> unit
(** Send a shutdown request to the LSP server and handle its response *)
