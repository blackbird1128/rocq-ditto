open Ditto

type process_status = Success | Failure of string

val run_process :
  env:string array ->
  args:string array ->
  string ->
  Unix.file_descr ->
  Unix.file_descr ->
  Unix.file_descr ->
  (unit, Error.t) result

val run_process_loud :
  env:string array -> args:string array -> string -> (unit, Error.t) result

val run_process_silent :
  env:string array -> args:string array -> string -> (unit, Error.t) result

val spawn_process : env:string array -> args:string array -> string -> int
val wait_for_one : unit -> int * process_status
val kill_all_running : (int, 'a) Hashtbl.t -> unit
