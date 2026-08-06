open Ditto

type process_status = Success | Failure of string

let string_of_process_status = function
  | Unix.WEXITED code -> Printf.sprintf "Exited with code %d" code
  | Unix.WSIGNALED signal -> Printf.sprintf "Killed by signal %d" signal
  | Unix.WSTOPPED signal -> Printf.sprintf "Stopped by signal %d" signal

let run_process ~(env : string array) ~(args : string array) (prog : string)
    (stdin : Unix.file_descr) (stdout : Unix.file_descr)
    (stderr : Unix.file_descr) : (unit, Error.t) result =
  let pid = Unix.create_process_env prog args env stdin stdout stderr in
  let _, status = Unix.waitpid [] pid in
  match status with
  | WEXITED 0 -> Ok ()
  | _ -> Error.string_to_or_error (string_of_process_status status)

let run_process_loud ~(env : string array) ~(args : string array)
    (prog : string) : (unit, Error.t) result =
  run_process ~env ~args prog Unix.stdin Unix.stdout Unix.stderr

let run_process_silent ~(env : string array) ~(args : string array)
    (prog : string) : (unit, Error.t) result =
  let devnull = Unix.openfile "/dev/null" [ Unix.O_WRONLY ] 0o666 in
  Fun.protect
    ~finally:(fun () -> try Unix.close devnull with Unix.Unix_error _ -> ())
    (fun () -> run_process ~env ~args prog devnull devnull devnull)

let spawn_process ~(env : string array) ~(args : string array) (prog : string) :
    int =
  let pid =
    Unix.create_process_env prog args env Unix.stdin Unix.stdout Unix.stderr
  in
  pid

let wait_for_one () : int * process_status =
  let pid, status = Unix.wait () in
  match status with
  | WEXITED 0 -> (pid, Success)
  | _ -> (pid, Failure (string_of_process_status status))

let kill_all_running (running : (int, 'a) Hashtbl.t) : unit =
  let pids = Hashtbl.to_seq_keys running |> List.of_seq in

  (* ask children to terminate *)
  List.iter (fun pid -> try Unix.kill pid Sys.sigterm with _ -> ()) pids;
  (* cleanup possible zombies *)
  List.iter (fun pid -> try ignore (Unix.waitpid [] pid) with _ -> ()) pids
