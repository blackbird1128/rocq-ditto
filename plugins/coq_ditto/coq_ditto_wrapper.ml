open Ditto_cli_lib.Cli
open Ditto_cli_lib.Plugin_configuration
open Ditto_cli_lib
open Ditto
open Cmdliner

type running_job = { target : string }

let warn_if_exists (dir_state : Filesystem.creation_status) =
  match dir_state with
  | AlreadyExists ->
      Logs.warn (fun m ->
          m "output directory already exists: replacing files\n%!")
  | _ -> ()

let make_args_transform_files (prog : string) (root : string) (verbose : bool)
    (save_vo : bool) (input_file : string) : string array =
  let args = [ prog; "--root=" ^ root; "--plugin=ditto-plugin"; input_file ] in
  let args =
    args @ [ (if verbose then "--display=verbose" else "--display=quiet") ]
  in
  let args = if save_vo then args @ [ "--no_vo" ] else args in
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
        Env.extend_env base_env
          [
            ("OUTPUT_FILENAME", curr_file);
            ("CURRENT_FILE_COUNT", string_of_int curr_file_count);
            ("TOTAL_FILE_COUNT", string_of_int total_file_count);
          ]
      in
      let* _status =
        Process_runner.run_process_loud ~env:curr_env ~args:curr_args prog
      in
      Printf.eprintf "\n%!";
      Ok (curr_file_count + 1))
    1 dep_files
  |> Result.map (fun _ -> ())

let compile_files (files : string list) (root : string)
    (base_env : string array) : (unit, Error.t) result =
  let ( let* ) = Result.bind in
  let prog = "fcc" in
  List_utils.fold_left_result
    (fun current_file_count curr_file ->
      Printf.eprintf "compiling file %s%!" curr_file;
      let curr_args = make_args_compile_files root curr_file in
      let* _status =
        Process_runner.run_process_silent ~env:base_env ~args:curr_args prog
      in
      Ok (current_file_count + 1))
    1 files
  |> Result.map (fun _ -> ())

let run_stats (opts : statistic_options) : (unit, Error.t) result =
  let input = opts.input in
  let input_dir =
    match Project.find_project input with
    | Some project -> Project.directory project
    | None -> Filename.dirname input
  in
  let statistic = statistic_kind_to_string opts.statistic in
  let format = opts.format in

  let env =
    Env.extend_env (Unix.environment ())
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
    let curr_env = Env.extend_env env [ ("OUTPUT_FILENAME", file) ] in
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

let with_dependencies ~(input_file : string) ~(project_dir : string) run =
  let ( let* ) = Result.bind in
  let* project = Project.require_project project_dir in
  let* dep_graph = Compile.coqproject_to_dep_graph project in
  let* dependencies =
    Dependency_graph.get_file_dependencies input_file dep_graph
  in
  run (Project.directory project) dependencies

let environment_of_settings (settings : transformation_settings) : string array =
  let verbose = settings.verbosity = Plugin_configuration.Verbose in
  let quiet = settings.verbosity = Plugin_configuration.Quiet in
  Env.extend_env (Unix.environment ())
    [
      ("DITTO_ACTION", "transform");
      ("DITTO_TRANSFORMATION", transformation_kind_to_string settings.transformation);
      ("DEBUG_LEVEL", string_of_bool verbose);
      ("SAVE_VO", string_of_bool settings.save_vo);
      ("QUIET", string_of_bool quiet);
      ("REVERSE_ORDER", string_of_bool settings.reverse_order);
      ("SUMMARY", string_of_bool settings.summary);
    ]

let transform_document (opts : document_options) : (unit, Error.t) result =
  let prog = "fcc" in

  let verbose = opts.settings.verbosity = Plugin_configuration.Verbose in
  let base_env = environment_of_settings opts.settings in

  let ( let* ) = Result.bind in
  let* _ =
    match opts.dependencies_action with
    | NoAction -> Ok ()
    | CompileDependencies ->
        with_dependencies ~input_file:opts.source ~project_dir:opts.source_directory
          (fun project deps ->
            Printf.eprintf "Compiling %d dependencies\n%!" (List.length deps);
            compile_files deps project (Unix.environment ()))
    | TransformDependencies ->
        with_dependencies ~input_file:opts.source ~project_dir:opts.source_directory
          (fun project deps ->
            let length_dep = List.length deps in
            Printf.eprintf "Transforming %d dependencies\n%!" length_dep;
            transform_files project deps "fcc" length_dep base_env true verbose)
  in

  let env = Env.extend_env base_env [ ("OUTPUT_FILENAME", opts.destination) ] in

  let args =
    make_args_transform_files prog opts.source_directory verbose opts.settings.save_vo
      opts.source
  in
  Process_runner.run_process_loud ~env ~args prog

let transform_project (opts : project_options) : (unit, Error.t) result =
  let ( let* ) = Result.bind in
  let prog = "fcc" in
  let verbose = opts.settings.verbosity = Plugin_configuration.Verbose in
  let base_env = environment_of_settings opts.settings in
  let* p = Project.read_project_file opts.project in

  let filenames =
    List.map
      (fun (x : string CoqProject_file.sourced) -> Filename.basename x.thing)
      p.files
  in

  let makefile_path =
    Filename.concat (Project.directory opts.project) "Makefile"
  in

  let* new_dir_state = Filesystem.make_dir opts.destination in
  warn_if_exists new_dir_state;
  let* _ =
    Filesystem.copy_dir opts.source_directory opts.destination filenames
  in
  let* _ =
    Filesystem.copy_file
      (Project.path opts.project)
      (Filename.concat opts.destination (Project.filename opts.project))
  in

  let* _ =
    if Sys.file_exists makefile_path then
      Filesystem.copy_file makefile_path
        (Filename.concat opts.destination "Makefile")
    else Ok ()
  in

  let* project =
    Project.find_project opts.destination
    |> Option_utils.to_result
         ~none:
           (Error.string_to_or_error "Can't find the newly created _CoqProject")
  in
  let* depgraph : Dependency_graph.t =
    Compile.coqproject_to_dep_graph project
  in

  let dependents = Dependency_graph.build_dependents depgraph in

  let outdeg_graph = Dependency_graph.build_outdegrees depgraph in

  run_parallel ~jobs:opts.jobs ~env:base_env ~prog ~root:opts.destination
    ~save_vo:opts.settings.save_vo ~verbose ~dependents ~outdegree:outdeg_graph

(* --- Cmdliner definitions ------------------------------------------- *)

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
            let message =
              message ^ Printf.sprintf "\n\nHint: did you mean '%s'?" suggestion
            in
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

let summary_t =
  Arg.(
    value & flag
    & info [ "s"; "summary" ] ~doc:"Output the number of emitted steps")

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
      summary dependencies_action jobs =
    {
      input;
      output;
      transformation;
      verbose;
      quiet;
      save_vo;
      reverse_order;
      summary;
      dependencies_action;
      jobs;
    }
  in

  let requested_options_t =
    Term.(
      const combine $ input_t $ output_t $ transformation_t $ verbose_t
      $ quiet_t $ save_vo_t $ reverse_order_t $ summary_t
      $ dependencies_action_t $ jobs_t)
  in

  Term.(const Cli.resolve $ requested_options_t)

let statistic_t =
  Arg.(
    required
    & opt (some statistic_kind_conv) None
    & info [ "s"; "statistic" ] ~docv:"KIND" ~doc:"statistic to compute")

let stats_options_t =
  let make input statistic format = { input; statistic; format } in
  Term.(const make $ input_t $ statistic_t $ output_format_t)

let result_to_exit (result : (unit, Error.t) result) : 'a =
  match result with
  | Ok () -> exit 0
  | Error err ->
      Logs.err (fun m -> m "%s" (Error.to_string_hum err));
      exit 1

let main (resolved : (operation, Error.t) result) =
  let ( let* ) = Result.bind in
  let result =
    let* op = resolved in
    let verbosity =
      match op with
      | TransformDocument opts -> opts.settings.verbosity
      | TransformProject opts -> opts.settings.verbosity
    in
    Logs.set_level
      (Some (if verbosity = Plugin_configuration.Verbose then Debug else Info));
    match op with
    | TransformDocument opts -> transform_document opts
    | TransformProject opts -> transform_project opts
  in
  result_to_exit result

let main_stats (opts : statistic_options) =
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
  let out = Format.err_formatter in
  let reporter =
    Logs_fmt.reporter ~pp_header:pp_header_no_app ~app:out ~dst:out ()
  in
  Logs.set_reporter reporter;
  Logs.set_level (Some Info);
  let exit_code = Cmd.eval cmd in
  exit exit_code
