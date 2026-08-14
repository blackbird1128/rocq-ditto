open Ditto

type process_status = Success | Failure of string
type pid

val string_of_pid : pid -> string

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

val spawn_process : env:string array -> args:string array -> string -> pid
val wait_for_one : unit -> pid * process_status
val kill_all_running : (pid, 'a) Hashtbl.t -> unit
