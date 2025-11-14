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
      print_endline "Warning: output directory already exists: replacing files"
  | _ -> ()

let transform_project (opts : cli_options) : (int, Error.t) result =
  let ( let* ) = Result.bind in
  let input = opts.input
  and output = opts.output
  and transformation = transformation_kind_to_string opts.transformation
  and verbose = opts.verbose
  and quiet = opts.quiet
  and save_vo = opts.save_vo
  and reverse_order = opts.reverse_order
  and skipped_files = opts.skipped_files in

  print_newline ();

  let out = Format.std_formatter in
  let reporter =
    Logs_fmt.reporter ~pp_header:pp_header_no_app ~app:out ~dst:out ()
  in
  Logs.set_reporter reporter;
  if verbose then Logs.set_level (Some Logs.Debug)
  else Logs.set_level (Some Logs.Info);

  let exec_name = Filename.basename Sys.argv.(0) in
  (match exec_name with
  | "coq-ditto" ->
      Logs.warn (fun m ->
          m
            "Alias coq-ditto might disappear in the future, please use \
             rocq-ditto instead")
  | _ -> ());

  let pathkind = Filesystem.get_pathkind input in

  if pathkind = File && List.length skipped_files > 0 then
    Error.string_to_or_error
      "Using --skip with a single file doesn't make sense"
  else if verbose && quiet then
    Error.string_to_or_error "Cannot use both --verbose and --quiet"
  else
    match pathkind with
    | File -> (
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

          let env =
            Array.append (Unix.environment ())
              [|
                "DITTO_TRANSFORMATION=" ^ transformation;
                "OUTPUT_FILENAME=" ^ output;
                "DEBUG_LEVEL=" ^ string_of_bool verbose;
                "SAVE_VO=" ^ string_of_bool save_vo;
                "QUIET=" ^ string_of_bool quiet;
                "REVERSE_ORDER=" ^ string_of_bool reverse_order;
              |]
          in
          let prog = "fcc" in
          let args =
            [| prog; "--root=" ^ input_dir; "--plugin=ditto-plugin"; input |]
          in
          let pid =
            Unix.create_process_env prog args env Unix.stdin Unix.stdout
              Unix.stderr
          in
          let _, status = Unix.waitpid [] pid in
          match status with
          | Unix.WEXITED 0 -> Ok 0
          | _ -> Error.string_to_or_error (string_of_process_status status))
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
            let files = List.map (fun x -> x.thing) p.files in
            let filenames = List.map Filename.basename files in
            let* dep_files = Compile.coqproject_sorted_files coqproject_path in
            let* new_dir_state = Filesystem.make_dir output in
            warn_if_exists new_dir_state;
            let* _ = Filesystem.copy_dir input output filenames in
            let* _ =
              Filesystem.copy_file coqproject_path
                (Filename.concat output coqproject_file)
            in
            let env =
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
            let args =
              [| prog; "--root=" ^ output; "--plugin=ditto-plugin" |]
            in
            let args =
              if verbose then Array.append args [| "--display=verbose" |]
              else args
            in
            let args =
              if save_vo then Array.append args [| "--no_vo" |] else args
            in
            let transformations_status =
              List.fold_left
                (fun err_acc x ->
                  match err_acc with
                  | Unix.WEXITED 0, _ ->
                      let rel_path = remove_prefix x input in
                      let curr_path = Filename.concat output rel_path in
                      let curr_args = Array.append args [| curr_path |] in
                      let curr_env =
                        Array.append env [| "OUTPUT_FILENAME=" ^ curr_path |]
                      in
                      let pid =
                        Unix.create_process_env prog curr_args curr_env
                          Unix.stdin Unix.stdout Unix.stderr
                      in
                      flush_all ();
                      let _, status = Unix.waitpid [] pid in
                      (status, x)
                  | err -> err)
                (Unix.WEXITED 0, "default")
                dep_files
            in
            if fst transformations_status != Unix.WEXITED 0 then
              Error.string_to_or_error
                (string_of_process_status (fst transformations_status)
                ^ " filename " ^ snd transformations_status)
            else Ok 0)

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
      print_endline "Available transformations:\n";
      print_endline (help_to_string transformations_help);
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
