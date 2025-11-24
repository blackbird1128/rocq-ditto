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
  skipped_files : string list;
}

let string_of_process_status = function
  | Unix.WEXITED code -> Printf.sprintf "Exited with code %d" code
  | Unix.WSIGNALED signal -> Printf.sprintf "Killed by signal %d" signal
  | Unix.WSTOPPED signal -> Printf.sprintf "Stopped by signal %d" signal

let remove_prefix (str : string) (prefix : string) =
  let prefix_len = String.length prefix in
  if String.length str >= prefix_len && String.sub str 0 prefix_len = prefix
  then String.sub str prefix_len (String.length str - prefix_len)
  else str

let warn_if_exists (dir_state : Filesystem.newDirState) =
  match dir_state with
  | AlreadyExists ->
      Printf.printf
        "Warning: output directory already exists: replacing files\n%!"
  | _ -> ()

let validate_opts opts pathkind =
  if pathkind = Filesystem.File && opts.skipped_files <> [] then
    Error.string_to_or_error
      "Using --skip with a single file doesn't make sense"
  else if opts.verbose && opts.quiet then
    Error.string_to_or_error "Cannot use both --verbose and --quiet"
  else Ok ()

let run_process ~(env : string array) ~(args : string array) (prog : string) =
  (* Open /dev/null for output redirection *)
  (* let devnull = Unix.openfile "/dev/null" [ Unix.O_WRONLY ] 0o666 in *)
  let pid =
    Unix.create_process_env prog args env Unix.stdin Unix.stdout Unix.stderr
  in
  let _, status = Unix.waitpid [] pid in
  match status with
  | WEXITED 0 -> Ok 0
  | _ -> Error.string_to_or_error (string_of_process_status status)

let make_args (prog : string) (root : string) (verbose : bool) (save_vo : bool)
    (input_file : string) =
  let base =
    [| prog; "--root=" ^ root; "--plugin=ditto-plugin"; input_file |]
  in
  base |> fun a ->
  if verbose then Array.append a [| "--display=verbose" |]
  else
    Array.append a [| "--display=quiet" |] |> fun a ->
    if save_vo then Array.append a [| "--no_vo" |] else a

let transform_project (opts : cli_options) : (int, Error.t) result =
  let ( let* ) = Result.bind in
  let input = opts.input
  and output = opts.output
  and transformation = transformation_kind_to_string opts.transformation
  and verbose = opts.verbose
  and quiet = opts.quiet
  and save_vo = opts.save_vo
  and reverse_order = opts.reverse_order in

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

  let* () = validate_opts opts pathkind in

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

        let env = Array.append base_env [| "OUTPUT_FILENAME=" ^ output |] in

        let args = make_args prog input_dir verbose save_vo input in
        run_process ~env ~args prog
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
          let* dep_graph = Compile.coqproject_to_dep_graph coqproject_path in

          let* new_dir_state = Filesystem.make_dir output in
          warn_if_exists new_dir_state;
          let* _ = Filesystem.copy_dir input output filenames in
          let* _ =
            Filesystem.copy_file coqproject_path
              (Filename.concat output coqproject_file)
          in

          let total_file_count = List.length dep_files in

          let transformations_status =
            List.fold_left
              (fun (err_acc, curr_file_count) curr_file ->
                match err_acc with
                | Ok 0 ->
                    let rel_path = remove_prefix curr_file input in
                    let curr_out_path = Filename.concat output rel_path in
                    let curr_args =
                      make_args prog output verbose save_vo curr_out_path
                    in
                    let curr_env =
                      Array.append base_env
                        [|
                          "OUTPUT_FILENAME=" ^ curr_out_path;
                          "CURRENT_FILE_COUNT=" ^ string_of_int curr_file_count;
                          "TOTAL_FILE_COUNT=" ^ string_of_int total_file_count;
                        |]
                    in
                    let status =
                      run_process ~env:curr_env ~args:curr_args prog
                    in
                    Printf.printf "\n%!";
                    (status, curr_file_count + 1)
                | err -> (err, curr_file_count + 1))
              (Ok 0, 1) dep_files
          in
          fst transformations_status)

(* --- Cmdliner definitions ------------------------------------------- *)

let transformation_kind_conv =
  let parse s =
    match arg_to_transformation_kind s with
    | Ok v -> Ok v
    | Error e -> Error (`Msg (Error.to_string_hum e))
  in
  let print fmt k = Format.fprintf fmt "%s" (transformation_kind_to_string k) in
  Cmdliner.Arg.conv (parse, print)

let string_list_conv =
  let parse s = Ok (String.split_on_char ' ' s |> List.filter (( <> ) "")) in
  let print fmt lst = Format.fprintf fmt "%s" (String.concat " " lst) in
  Arg.conv (parse, print)

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

let skip_t =
  let doc = "Files to skip (can be given multiple times)." in
  Arg.(value & opt_all string [] & info [ "skip" ] ~docv:"FILE" ~doc)

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

let cli_options_t =
  let combine input output transformation verbose quiet save_vo reverse_order
      skipped_files =
    {
      input;
      output;
      transformation;
      verbose;
      quiet;
      save_vo;
      reverse_order;
      skipped_files;
    }
  in
  Term.(
    const combine $ input_t $ output_t $ transformation_t $ verbose_t $ quiet_t
    $ save_vo_t $ reverse_order_t $ skip_t)

let main opts =
  match opts.transformation with
  | Help ->
      Printf.printf "Available transformations:\n";
      Printf.printf "%s\n%!" (help_to_string transformations_help);
      exit 0
  | _ -> (
      match transform_project opts with
      | Ok res -> exit res
      | Error err ->
          prerr_endline (Error.to_string_hum err);
          exit 1)

let cmd =
  let doc = "Apply transformations to Coq projects or files." in
  Cmd.v (Cmd.info "rocq-ditto" ~doc) Term.(const main $ cli_options_t)

let () = exit (Cmd.eval cmd)
