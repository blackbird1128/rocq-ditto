open Ditto_cli_lib.Cli
open Ditto
open Cmdliner

type cli_options = {
  input : string;
  output : string;
  transformation : transformation_kind;
  verbose : bool;
  quiet : bool;
  save_vo : bool;
  reverse_order : bool;
  dependencies_action : dependencies_action;
  jobs : int option;
}

type process_status = Success | Failure of string
type running_job = { target : string }

let string_of_process_status = function
  | Unix.WEXITED code -> Printf.sprintf "Exited with code %d" code
  | Unix.WSIGNALED signal -> Printf.sprintf "Killed by signal %d" signal
  | Unix.WSTOPPED signal -> Printf.sprintf "Stopped by signal %d" signal

let warn_if_exists (dir_state : Filesystem.newDirState) =
  match dir_state with
  | AlreadyExists ->
      Printf.printf
        "Warning: output directory already exists: replacing files\n%!"
  | _ -> ()

let validate_opts (opts : cli_options) (pathkind : Filesystem.path_kind) =
  if opts.dependencies_action != NoAction && pathkind = Filesystem.Dir then
    Error.string_to_or_error
      "Using a dependency action when targeting a folder doesn't make sense"
  else if Option.has_some opts.jobs && pathkind = Filesystem.File then
    Error.string_to_or_error "Cannot use --jobs on a single file"
  else if opts.verbose && opts.quiet then
    Error.string_to_or_error "Cannot use both --verbose and --quiet"
  else Ok ()

let spawn_process ~(env : string array) ~(args : string array) (prog : string) =
  let pid =
    Unix.create_process_env prog args env Unix.stdin Unix.stdout Unix.stderr
  in
  pid

let wait_for_one () : int * process_status =
  let pid, status = Unix.wait () in
  match status with
  | WEXITED 0 -> (pid, Success)
  | _ -> (pid, Failure (string_of_process_status status))

let run_process ~(env : string array) ~(args : string array) (prog : string)
    (stdin : Unix.file_descr) (stdout : Unix.file_descr)
    (stderr : Unix.file_descr) =
  let pid = Unix.create_process_env prog args env stdin stdout stderr in
  let _, status = Unix.waitpid [] pid in
  match status with
  | WEXITED 0 -> Ok ()
  | _ -> Error.string_to_or_error (string_of_process_status status)

let run_process_loud ~(env : string array) ~(args : string array)
    (prog : string) =
  run_process ~env ~args prog Unix.stdin Unix.stdout Unix.stderr

let run_process_silent ~(env : string array) ~(args : string array)
    (prog : string) =
  let devnull = Unix.openfile "/dev/null" [ Unix.O_WRONLY ] 0o666 in
  run_process ~env ~args prog devnull devnull devnull

let make_args_transform_files (prog : string) (root : string) (verbose : bool)
    (save_vo : bool) (input_file : string) =
  let base =
    [| prog; "--root=" ^ root; "--plugin=ditto-plugin"; input_file |]
  in
  base |> fun a ->
  if verbose then Array.append a [| "--display=verbose" |]
  else
    Array.append a [| "--display=quiet" |] |> fun a ->
    if save_vo then Array.append a [| "--no_vo" |] else a

let make_args_compile_files (root : string) (input_file : string) =
  [| "fcc"; "--root=" ^ root; input_file |]

let kill_all_running (running : (int, 'a) Hashtbl.t) =
  Hashtbl.iter
    (fun pid _ -> try Unix.kill pid Sys.sigterm with _ -> ())
    running

let run_parallel ~(jobs : int) ~(prog : string) ~(env : string array)
    ~(root : string) ~(verbose : bool) ~(save_vo : bool)
    ~(dependents : (string, string list) Hashtbl.t)
    ~(indegree : (string, int) Hashtbl.t) : (unit, Error.t) result =
  let ready = Queue.create () in
  let running : (int, running_job) Hashtbl.t = Hashtbl.create 32 in

  let total_nodes = Hashtbl.length indegree in
  let completed = ref 0 in
  let failed = ref None in

  Hashtbl.iter
    (fun file degree -> if degree = 0 then Queue.add file ready else ())
    indegree;

  let spawn_for_file (file : string) =
    let curr_args = make_args_transform_files prog root verbose save_vo file in
    let curr_env = Array.append env [| "OUTPUT_FILENAME=" ^ file |] in
    let pid = spawn_process ~env:curr_env ~args:curr_args prog in
    let running_job = { target = file } in
    Hashtbl.add running pid running_job
  in

  let fill_slots () =
    while Hashtbl.length running < jobs && not (Queue.is_empty ready) do
      let file = Queue.take ready in
      spawn_for_file file
    done
  in

  let mark_done (file : string) =
    incr completed;
    let dependents_on = Hashtbl.find_all dependents file |> List.concat in
    List.iter
      (fun dep ->
        match Hashtbl.find_opt indegree dep with
        | None -> ()
        | Some degree ->
            let d' = degree - 1 in
            Hashtbl.replace indegree dep d';
            if d' = 0 then Queue.add dep ready)
      dependents_on
  in

  let rec loop () =
    match !failed with
    | Some failure -> Error.string_to_or_error failure
    | None -> (
        fill_slots ();
        if !completed = total_nodes then Ok ()
        else if Hashtbl.length running = 0 then
          Error.string_to_or_error
            "something went wrong: no runnable jobs, but build not complete"
        else
          let pid, status = wait_for_one () in
          match Hashtbl.find_opt running pid with
          | None ->
              Error.format_to_or_error "Unknown child process finished: pid: %d"
                pid
          | Some job -> (
              Hashtbl.remove running pid;
              match status with
              | Success ->
                  mark_done job.target;
                  loop ()
              | Failure msg ->
                  failed := Some (Printf.sprintf "%s failed: %s" job.target msg);
                  kill_all_running running;
                  Error.format_to_or_error "%s failed: %s" job.target msg))
  in

  loop ()

let transform_files (root : string) (dep_files : string list) (prog : string)
    (total_file_count : int) (base_env : string array) (save_vo : bool)
    (verbose : bool) =
  List.fold_left
    (fun (err_acc, curr_file_count) curr_file ->
      match err_acc with
      | Ok () ->
          let curr_args =
            make_args_transform_files prog root verbose save_vo curr_file
          in
          let curr_env =
            Array.append base_env
              [|
                "OUTPUT_FILENAME=" ^ curr_file;
                "CURRENT_FILE_COUNT=" ^ string_of_int curr_file_count;
                "TOTAL_FILE_COUNT=" ^ string_of_int total_file_count;
              |]
          in
          let status = run_process_loud ~env:curr_env ~args:curr_args prog in
          Printf.printf "\n%!";
          (status, curr_file_count + 1)
      | err -> (err, curr_file_count + 1))
    (Ok (), 1) dep_files

let compile_files (files : string list) (root : string) =
  let prog = "fcc" in
  List.fold_left
    (fun (err_acc, curr_file_count) curr_file ->
      match err_acc with
      | Ok () ->
          Printf.printf "compiling file %s\n%!" curr_file;
          let curr_args = make_args_compile_files root curr_file in
          let status = run_process_silent ~env:[||] ~args:curr_args prog in
          (status, curr_file_count + 1)
      | err -> (err, curr_file_count + 1))
    (Ok (), 1) files

let transform_project (opts : cli_options) : (unit, Error.t) result =
  let ( let* ) = Result.bind in
  let input = opts.input
  and output = opts.output
  and transformation = transformation_kind_to_string opts.transformation
  and verbose = opts.verbose
  and quiet = opts.quiet
  and save_vo = opts.save_vo
  and reverse_order = opts.reverse_order
  and jobs_opt = opts.jobs in

  let out = Format.std_formatter in
  let reporter =
    Logs_fmt.reporter ~pp_header:pp_header_no_app ~app:out ~dst:out ()
  in
  Logs.set_reporter reporter;
  Logs.set_level (Some (if verbose then Debug else Info));

  let exec_name = Filename.basename Sys.argv.(0) in
  (match exec_name with
  | "coq-ditto" ->
      Logs.warn (fun m ->
          m
            "Alias coq-ditto might disappear in the future, please use \
             rocq-ditto instead")
  | _ -> ());

  let pathkind = Filesystem.get_pathkind input in

  let _ = validate_opts opts pathkind in

  let base_env =
    Array.append (Unix.environment ())
      [|
        "DITTO_TRANSFORMATION=" ^ transformation;
        "DEBUG_LEVEL=" ^ string_of_bool verbose;
        "SAVE_VO=" ^ string_of_bool save_vo;
        "QUIET=" ^ string_of_bool quiet;
        "REVERSE_ORDER=" ^ string_of_bool reverse_order;
      |]
  in

  let jobs = Option.default 1 jobs_opt in

  let prog = "fcc" in
  match pathkind with
  | File ->
      if Filesystem.is_directory output then
        Error.string_to_or_error
          "Output must be a filename when input is a file"
      else if not (Sys.file_exists input) then
        Error.string_to_or_error "Input must be an existing file"
      else
        let coqproject_opt = Compile.find_coqproject_dir_and_file input in

        let input_dir =
          match coqproject_opt with
          | Some (dir, _) -> dir
          | None -> Filename.dirname input
        in

        let* _ =
          match opts.dependencies_action with
          | NoAction -> Ok ()
          | CompileDependencies -> (
              match coqproject_opt with
              | None ->
                  Error.string_to_or_error
                    "No _CoqProject or _RocqProject found, impossible to run a \
                     dependency action"
              | Some (dir, file) ->
                  let* dep_graph =
                    Compile.coqproject_to_dep_graph (Filename.concat dir file)
                  in
                  let dependencies =
                    Compile.get_file_dependencies input dep_graph
                  in
                  Printf.printf "Compiling %d dependencies\n%!"
                    (List.length dependencies);
                  let res, _ = compile_files dependencies dir in
                  res)
          | TransformDependencies -> (
              match coqproject_opt with
              | None ->
                  Error.string_to_or_error
                    "No _CoqProject or _RocqProject found, impossible to run a \
                     dependency action"
              | Some (dir, file) ->
                  let* dep_graph =
                    Compile.coqproject_to_dep_graph (Filename.concat dir file)
                  in
                  let dependencies =
                    Compile.get_file_dependencies input dep_graph
                  in
                  let length_dep = List.length dependencies in
                  Printf.printf "Transforming %d dependencies\n%!" length_dep;
                  let res, _ =
                    transform_files dir dependencies "fcc" length_dep base_env
                      true verbose
                  in
                  res)
        in

        let env = Array.append base_env [| "OUTPUT_FILENAME=" ^ output |] in

        let args =
          make_args_transform_files prog input_dir verbose save_vo input
        in
        run_process_loud ~env ~args prog
  | Dir -> (
      match Compile.find_coqproject_dir_and_file input with
      | None ->
          Error.format_to_or_error
            "No _CoqProject or _RocqProject file found in %s" input
      | Some (coqproject_dir, coqproject_file) ->
          let coqproject_path =
            Filename.concat coqproject_dir coqproject_file
          in

          let open CoqProject_file in
          let p =
            CoqProject_file.read_project_file
              ~warning_fn:(fun _ -> ())
              coqproject_path
          in

          let filenames =
            List.map (fun x -> Filename.basename x.thing) p.files
          in

          let* dep_files = Compile.coqproject_sorted_files coqproject_path in
          let dep_files_out =
            List.map
              (fun file ->
                let rel_file_path = String_utils.remove_prefix file input in
                let out_path = Filename.concat output rel_file_path in

                out_path)
              dep_files
          in

          let makefile_path = Filename.concat coqproject_dir "Makefile" in

          let* new_dir_state = Filesystem.make_dir output in
          warn_if_exists new_dir_state;
          let* _ = Filesystem.copy_dir input output filenames in
          let* _ =
            Filesystem.copy_file coqproject_path
              (Filename.concat output coqproject_file)
          in

          let* _ =
            if Sys.file_exists makefile_path then
              Filesystem.copy_file makefile_path
                (Filename.concat output "Makefile")
            else Ok ()
          in

          let coqproject_dir_out, coqproject_file_out =
            Compile.find_coqproject_dir_and_file output |> Option.get
          in
          let coqproject_out_path =
            Filename.concat coqproject_dir_out coqproject_file_out
          in

          let* depgraph : (string, string list) Hashtbl.t =
            Compile.coqproject_to_dep_graph coqproject_out_path
          in
          let _pad_depgraph =
            List.iter
              (fun x ->
                if not (Hashtbl.mem depgraph x) then Hashtbl.add depgraph x [])
              dep_files_out
          in

          let dependents = Compile.build_dependents depgraph in

          let indeg_graph = Compile.build_indegrees depgraph in

          run_parallel ~jobs ~env:base_env ~prog ~root:output ~save_vo ~verbose
            ~dependents ~indegree:indeg_graph)

(* --- Cmdliner definitions ------------------------------------------- *)

let transformation_kind_conv =
  let parse s =
    match arg_to_transformation_kind s with
    | Ok v -> Ok v
    | Error e -> Error (`Msg (Error.to_string_hum e))
  in
  let print fmt k = Format.fprintf fmt "%s" (transformation_kind_to_string k) in
  Cmdliner.Arg.conv (parse, print)

let dependencies_action_conv =
  let parse s =
    match arg_to_dependencies_action s with
    | Ok v -> Ok v
    | Error e -> Error (`Msg (Error.to_string_hum e))
  in
  let print fmt k = Format.fprintf fmt "%s" (dependencies_action_to_string k) in
  Cmdliner.Arg.conv (parse, print)

let input_t =
  let doc = "Input folder or filename." in
  Arg.(
    required
    & opt (some filepath) None
    & info [ "i"; "input" ] ~docv:"PATH" ~doc)

let output_t =
  let doc = "Output folder or filename." in
  Arg.(
    required
    & opt (some filepath) None
    & info [ "o"; "output" ] ~docv:"PATH" ~doc)

let transformation_t =
  let doc = "Transformation to apply." in
  Arg.(
    required
    & opt (some transformation_kind_conv) None
    & info [ "t"; "transformation" ] ~docv:"KIND" ~doc)

let dependencies_action_t =
  let doc =
    "Action to apply on the dependencies (only when targeting a single file)"
  in
  Arg.(
    value
    & opt dependencies_action_conv NoAction
    & info [ "a"; "action" ] ~docv:"ACTION" ~doc)

let verbose_t =
  Arg.(value & flag & info [ "v"; "verbose" ] ~doc:"Enable verbose output.")

let quiet_t =
  Arg.(value & flag & info [ "quiet" ] ~doc:"Suppress non-error output.")

let save_vo_t =
  Arg.(value & flag & info [ "save-vo" ] ~doc:"Save .vo of transformed file.")

let reverse_order_t =
  Arg.(
    value & flag
    & info [ "reverse-order" ]
        ~doc:
          "Reverse the order of proof processing to improve cache hits (may \
           produce invalid output).")

let positive_int =
  let parse s =
    match int_of_string_opt s with
    | Some n when n > 0 -> Ok n
    | Some _ -> Error (`Msg "must be a positive integer")
    | None -> Error (`Msg "invalid integer")
  in
  let print fmt n = Format.fprintf fmt "%d" n in
  Arg.conv (parse, print)

let jobs_t =
  let doc = "Number of jobs to run in parallel (> 0)." in
  Arg.(
    value & opt (some positive_int) None & info [ "j"; "jobs" ] ~docv:"N" ~doc)

let cli_options_t =
  let combine input output transformation verbose quiet save_vo reverse_order
      dependencies_action jobs =
    {
      input;
      output;
      transformation;
      verbose;
      quiet;
      save_vo;
      reverse_order;
      dependencies_action;
      jobs;
    }
  in
  Term.(
    const combine $ input_t $ output_t $ transformation_t $ verbose_t $ quiet_t
    $ save_vo_t $ reverse_order_t $ dependencies_action_t $ jobs_t)

let main (opts : cli_options) =
  match transform_project opts with
  | Ok _ -> exit 0
  | Error err ->
      prerr_endline (Error.to_string_hum err);
      exit 1

let print_transformation (kind, description) =
  Printf.printf "%s\n  %s\n\n" (transformation_kind_to_string kind) description

let list_transformations () =
  List.iter print_transformation transformations_help

(* let list_transformations () = *)
(*   Printf.printf "Available transformations:\n\n%s%!" *)
(*     (help_to_string transformations_help) *)

let list_cmd =
  let doc = "List the available transformations." in
  Cmd.v (Cmd.info "list" ~doc) Term.(const list_transformations $ const ())

let default_term = Term.(const main $ cli_options_t)

let cmd =
  let doc = "Apply transformations to Rocq projects or files" in
  let info = Cmd.info "rocq-ditto" ~doc in
  Cmd.group ~default:default_term info [ list_cmd ]

let () = exit (Cmd.eval cmd)
