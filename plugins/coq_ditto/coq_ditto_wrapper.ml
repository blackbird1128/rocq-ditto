open Ditto_cli_lib.Cli
open Ditto
open Cmdliner

type transformation_options = {
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

type stats_option = {
  input : string;
  statistic : statistic_kind;
  format : output_format;
}

type running_job = { target : string }

let warn_if_exists (dir_state : Filesystem.creation_status) =
  match dir_state with
  | AlreadyExists ->
      Printf.printf
        "Warning: output directory already exists: replacing files\n%!"
  | _ -> ()

let validate_transformation_opts (opts : transformation_options)
    (pathkind : Filesystem.path_kind) =
  if opts.input = opts.output then
    Error.string_to_or_error "Input folder is equal to output folder, aborting"
  else if opts.dependencies_action != NoAction && pathkind = Filesystem.Dir then
    Error.string_to_or_error
      "Using a dependency action when targeting a folder doesn't make sense"
  else if Option.has_some opts.jobs && pathkind = Filesystem.File then
    Error.string_to_or_error "Cannot use --jobs on a single file"
  else if opts.verbose && opts.quiet then
    Error.string_to_or_error "Cannot use both --verbose and --quiet"
  else Ok ()

(* Already set values take precedence *)
(* TODO: check if this is the better solution *)
let add_to_env_preserving (env : string array) (assoc : string * string) :
    string array =
  let key, value = assoc in
  let env_list = Array.to_list env in
  let assoc_key_repr = Printf.sprintf "%s=" key in
  let assoc_repr = assoc_key_repr ^ value in
  match
    List.find_opt
      (fun env_val -> String.starts_with ~prefix:assoc_key_repr env_val)
      env_list
  with
  | Some _ -> env
  | None -> Array.of_list (assoc_repr :: env_list)

(* Already set values take precedence *)
(* TODO: check if this is the better solution *)
let extend_env (env_array : string array) (values : (string * string) list) :
    string array =
  List.fold_left
    (fun env_acc assoc -> add_to_env_preserving env_acc assoc)
    env_array values

let make_args_transform_files (prog : string) (root : string) (verbose : bool)
    (save_vo : bool) (input_file : string) : string array =
  let args = [ prog; "--root=" ^ root; "--plugin=ditto-plugin"; input_file ] in
  let args =
    args @ [ (if verbose then "--display=verbose" else "--display=quiet") ]
  in
  let args = if save_vo then args @ [ "--no-vo" ] else args in
  Array.of_list args

let make_args_compile_files (root : string) (input_file : string) =
  [| "fcc"; "--root=" ^ root; input_file |]

let transform_files (root : string) (dep_files : string list) (prog : string)
    (total_file_count : int) (base_env : string array) (save_vo : bool)
    (verbose : bool) : (unit, Error.t) result =
  let ( let* ) = Result.bind in
  List_utils.fold_left_result
    (fun curr_file_count curr_file ->
      let curr_args =
        make_args_transform_files prog root verbose save_vo curr_file
      in
      let curr_env =
        extend_env base_env
          [
            ("OUTPUT_FILENAME", curr_file);
            ("CURRENT_FILE_COUNT", string_of_int curr_file_count);
            ("TOTAL_FILE_COUNT", string_of_int total_file_count);
          ]
      in
      let* _status =
        Process_runner.run_process_loud ~env:curr_env ~args:curr_args prog
      in
      Printf.printf "\n%!";
      Ok (curr_file_count + 1))
    1 dep_files
  |> Result.map (fun _ -> ())

let compile_files (files : string list) (root : string) : (unit, Error.t) result
    =
  let ( let* ) = Result.bind in
  let prog = "fcc" in
  List_utils.fold_left_result
    (fun current_file_count curr_file ->
      Printf.printf "compiling file %s%!" curr_file;
      let curr_args = make_args_compile_files root curr_file in
      let* _status =
        Process_runner.run_process_silent ~env:(Unix.environment ())
          ~args:curr_args prog
      in
      Ok (current_file_count + 1))
    1 files
  |> Result.map (fun _ -> ())

let run_stats (opts : stats_option) : (unit, Error.t) result =
  let input = opts.input in
  let input_dir = Filename.dirname opts.input in
  let statistic = statistic_kind_to_string opts.statistic in
  let format = opts.format in

  let env =
    extend_env (Unix.environment ())
      [
        ("DITTO_ACTION", "statistics");
        ("DITTO_STATISTIC", statistic);
        ("DITTO_STAT_FORMAT", output_format_to_string format);
      ]
  in
  let args =
    [|
      "fcc";
      "--root=" ^ input_dir;
      "--plugin=ditto-plugin";
      input;
      "--display=quiet";
    |]
  in

  Process_runner.run_process_loud ~env ~args "fcc"

let run_parallel ~(jobs : int) ~(prog : string) ~(env : string array)
    ~(root : string) ~(verbose : bool) ~(save_vo : bool)
    ~(dependents : (string, string list) Hashtbl.t)
    ~(outdegree : (string, int) Hashtbl.t) : (unit, Error.t) result =
  let running : (Process_runner.pid, running_job) Hashtbl.t =
    Hashtbl.create 32
  in

  let total_nodes = Hashtbl.length outdegree in
  let completed = ref 0 in

  let initial_ready =
    Hashtbl.to_seq outdegree
    |> Seq.filter_map (fun (file, degree) ->
        if degree = 0 then Some file else None)
    |> List.of_seq |> List.sort String.compare
  in

  let ready = Queue.create () in
  List.iter (fun file -> Queue.add file ready) initial_ready;

  let spawn_for_file (file : string) =
    let curr_args = make_args_transform_files prog root verbose save_vo file in
    let curr_env = extend_env env [ ("OUTPUT_FILENAME", file) ] in
    let pid = Process_runner.spawn_process ~env:curr_env ~args:curr_args prog in
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
    let dependents_on =
      Hashtbl.find_all dependents file
      |> List.concat |> List.sort String.compare
    in
    List.iter
      (fun dep ->
        match Hashtbl.find_opt outdegree dep with
        | None -> ()
        | Some degree ->
            let d' = degree - 1 in
            Hashtbl.replace outdegree dep d';
            if d' = 0 then Queue.add dep ready)
      dependents_on
  in

  let rec loop () =
    fill_slots ();
    if !completed = total_nodes then Ok ()
    else if Hashtbl.length running = 0 then
      Error.string_to_or_error
        "something went wrong: no runnable jobs, but build not complete"
    else
      let pid, status = Process_runner.wait_for_one () in
      match Hashtbl.find_opt running pid with
      | None ->
          Error.format_to_or_error "Unknown child process finished: pid: %s"
            (Process_runner.string_of_pid pid)
      | Some job -> (
          Hashtbl.remove running pid;
          match status with
          | Success ->
              mark_done job.target;
              loop ()
          | Failure msg ->
              Process_runner.kill_all_running running;
              Error.format_to_or_error "%s failed: %s" job.target msg)
  in

  loop ()

let transform_project (opts : transformation_options) : (unit, Error.t) result =
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

  let* _ = validate_transformation_opts opts pathkind in

  let base_env =
    extend_env (Unix.environment ())
      [
        ("DITTO_ACTION", "transform");
        ("DITTO_TRANSFORMATION", transformation);
        ("DEBUG_LEVEL", string_of_bool verbose);
        ("SAVE_VO", string_of_bool save_vo);
        ("QUIET", string_of_bool quiet);
        ("REVERSE_ORDER", string_of_bool reverse_order);
      ]
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
        let coqproject_opt = Project.find_coqproject_dir_and_file input in

        let input_dir =
          match coqproject_opt with
          | Some { directory; _ } -> directory
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
              | Some project ->
                  let* dep_graph = Compile.coqproject_to_dep_graph project in
                  let* dependencies =
                    Dependency_graph.get_file_dependencies input dep_graph
                  in
                  Printf.printf "Compiling %d dependencies\n%!"
                    (List.length dependencies);
                  compile_files dependencies project.directory)
          | TransformDependencies -> (
              match coqproject_opt with
              | None ->
                  Error.string_to_or_error
                    "No _CoqProject or _RocqProject found, impossible to run a \
                     dependency action"
              | Some project ->
                  let* dep_graph = Compile.coqproject_to_dep_graph project in
                  let* dependencies =
                    Dependency_graph.get_file_dependencies input dep_graph
                  in
                  let length_dep = List.length dependencies in
                  Printf.printf "Transforming %d dependencies\n%!" length_dep;

                  transform_files project.directory dependencies "fcc"
                    length_dep base_env true verbose)
        in

        let env = extend_env base_env [ ("OUTPUT_FILENAME", output) ] in

        let args =
          make_args_transform_files prog input_dir verbose save_vo input
        in
        Process_runner.run_process_loud ~env ~args prog
  | Dir -> (
      match Project.find_coqproject_dir_and_file input with
      | None ->
          Error.format_to_or_error
            "No _CoqProject or _RocqProject file found in %s" input
      | Some project ->
          let* p = Project.read_project_file project in

          let filenames =
            List.map
              (fun (x : string CoqProject_file.sourced) ->
                Filename.basename x.thing)
              p.files
          in

          let makefile_path = Filename.concat project.directory "Makefile" in

          let* new_dir_state = Filesystem.make_dir output in
          warn_if_exists new_dir_state;
          let* _ = Filesystem.copy_dir input output filenames in
          let* _ =
            Filesystem.copy_file project.path
              (Filename.concat output project.filename)
          in

          let* _ =
            if Sys.file_exists makefile_path then
              Filesystem.copy_file makefile_path
                (Filename.concat output "Makefile")
            else Ok ()
          in

          let* project =
            Project.find_coqproject_dir_and_file output
            |> Option_utils.to_result
                 ~none:
                   (Error.string_to_or_error
                      "Can't find the newly created _CoqProject")
          in
          let* depgraph : Dependency_graph.t =
            Compile.coqproject_to_dep_graph project
          in

          let dependents = Dependency_graph.build_dependents depgraph in

          let outdeg_graph = Dependency_graph.build_outdegrees depgraph in

          run_parallel ~jobs ~env:base_env ~prog ~root:output ~save_vo ~verbose
            ~dependents ~outdegree:outdeg_graph)

(* --- Cmdliner definitions ------------------------------------------- *)

let transformation_suggestion = ref None

let transformation_kind_conv =
  let transformations =
    all_transformation_kinds
    |> List.map (fun kind -> (transformation_kind_to_string kind, kind))
  in
  let enum = Cmdliner.Arg.enum transformations in
  let enum_parser = Cmdliner.Arg.Conv.parser enum in
  let parse arg =
    match enum_parser arg with
    | Ok _ as result -> result
    | Error _ -> (
        let message =
          Printf.sprintf "invalid transformation %S, expected one of %s" arg
            (String.concat ", " transformations_list)
        in
        let suggestions =
          String.spellcheck
            (fun yield -> List.iter yield transformations_list)
            (String.lowercase_ascii arg)
        in
        match suggestions with
        | suggestion :: _ ->
            transformation_suggestion := Some suggestion;
            Error message
        | [] -> Error message)
  in
  Cmdliner.Arg.Conv.of_conv ~parser:parse enum

let statistic_kind_conv =
  let parse value =
    match arg_to_statistic_kind value with
    | Ok s -> Ok s
    | Error e -> Error (`Msg (Error.to_string_hum e))
  in
  let print fmt k = Format.fprintf fmt "%s" (statistic_kind_to_string k) in
  Cmdliner.Arg.conv (parse, print)

let dependencies_action_conv =
  let parse s =
    match arg_to_dependencies_action s with
    | Ok v -> Ok v
    | Error e -> Error (`Msg (Error.to_string_hum e))
  in
  let print fmt k = Format.fprintf fmt "%s" (dependencies_action_to_string k) in
  Cmdliner.Arg.conv (parse, print)

let output_format_conv =
  let parse s =
    match arg_to_output_format s with
    | Ok v -> Ok v
    | Error e -> Error (`Msg (Error.to_string_hum e))
  in
  let print fmt k = Format.fprintf fmt "%s" (output_format_to_string k) in
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

let output_format_t =
  let doc = "Statistic output format." in
  Arg.(
    value & opt output_format_conv Text & info [ "f"; "format" ] ~docv:"F" ~doc)

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

let transformation_options_t =
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

let statistic_t =
  Arg.(
    required
    & opt (some statistic_kind_conv) None
    & info [ "s"; "statistic" ] ~docv:"KIND" ~doc:"statistic to compute")

let stats_options_t =
  let make input statistic format = { input; statistic; format } in
  Term.(const make $ input_t $ statistic_t $ output_format_t)

let main (opts : transformation_options) =
  match transform_project opts with
  | Ok _ -> exit 0
  | Error err ->
      Logs.err (fun m -> m "%s" (Error.to_string_hum err));
      exit 1

let main_stats (opts : stats_option) =
  match run_stats opts with
  | Ok _ -> exit 0
  | Error err ->
      prerr_endline (Error.to_string_hum err);
      exit 1

let print_transformation (kind, description) =
  Printf.printf "%s\n  %s\n\n" (transformation_kind_to_string kind) description

let list_transformations () =
  List.iter print_transformation transformations_help

let transformation_man =
  [ `S "TRANSFORMATIONS" ]
  @ List.map
      (fun (kind, description) ->
        `I (transformation_kind_to_string kind, description))
      transformations_help

let list_cmd =
  let doc = "List the available transformations." in
  Cmd.v (Cmd.info "list" ~doc) Term.(const list_transformations $ const ())

let stats_cmd =
  let doc = "Compute statistics about a Rocq document." in
  Cmd.v (Cmd.info "stats" ~doc) Term.(const main_stats $ stats_options_t)

let default_term = Term.(const main $ transformation_options_t)

let cmd =
  let doc = "Transform and analyses Rocq projects or files" in
  let info = Cmd.info "rocq-ditto" ~man:transformation_man ~doc in
  Cmd.group ~default:default_term info [ list_cmd; stats_cmd ]

let () =
  let exit_code = Cmd.eval cmd in
  Option.iter
    (fun suggestion -> Printf.eprintf "Hint: did you mean '%s'?\n%!" suggestion)
    !transformation_suggestion;
  exit exit_code
