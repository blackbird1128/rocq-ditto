open Ditto

type transformation_kind =
  | Help
  | ExplicitFreshVariables
  | TurnIntoOneliner
  | ReplaceAutoWithSteps
  | CompressIntro
  | IdTransformation
[@@deriving variants]

let camel_to_snake (s : string) : string =
  let b = Buffer.create (String.length s * 2) in
  String.iteri
    (fun i c ->
      if 'A' <= c && c <= 'Z' then (
        if i > 0 then Buffer.add_char b '_';
        Buffer.add_char b (Char.lowercase_ascii c))
      else Buffer.add_char b c)
    s;
  Buffer.contents b

let transformation_kind_to_string (kind : transformation_kind) : string =
  Variants_of_transformation_kind.to_name kind |> camel_to_snake

let input_arg = ref ""
let output_arg = ref ""
let transformation_arg = ref ""
let verbose = ref false
let save_vo = ref false
let quiet = ref false

let transformations_help =
  [
    ( ExplicitFreshVariables,
      "replace call to tactics creating fresh variables such as intros with \
       intros V_1  V_2 V_n\n\
       where each V_i corresponds to a variable automatically introduced by \
       the tactic." );
    ( TurnIntoOneliner,
      "Remove all commands from the proof and turn all steps into a single \
       tactic call using the ';' and '[]' tacticals." );
    ( ReplaceAutoWithSteps,
      "Replace all calls to the 'auto' tactic with the steps effectively used \
       by auto using 'info_auto' trace." );
    ( CompressIntro,
      "Replace consecutive calls to the 'intro' tactic with one call to \
       'intros'." );
    (IdTransformation, "Keep the file the same.");
  ]

let arg_to_transformation_kind (arg : string) :
    (transformation_kind, string) result =
  let normalized = String.lowercase_ascii arg in
  if normalized = "help" then Ok Help
  else if normalized = "explicit_fresh_variables" then Ok ExplicitFreshVariables
  else if normalized = "turn_into_oneliner" then Ok TurnIntoOneliner
  else if normalized = "replace_auto_with_steps" then Ok ReplaceAutoWithSteps
  else if normalized = "compress_intro" then Ok CompressIntro
  else if normalized = "id_transformation" then Ok IdTransformation
  else
    Error
      ("transformation " ^ arg ^ " wasn't recognized as a valid transformation")

let help_to_string (transformation_help : (transformation_kind * string) list) :
    string =
  List.fold_left
    (fun acc (kind, help) ->
      acc ^ (transformation_kind_to_string kind ^ ": " ^ help) ^ "\n")
    "" transformation_help

let rec copy_dir (src : string) (dst : string) (filenames_to_copy : string list)
    : (unit, Error.t) result =
  (* ensure target dir exists *)
  (try Unix.mkdir dst 0o755 with Unix.Unix_error (EEXIST, _, _) -> ());

  let dh = Unix.opendir src in
  let rec loop () =
    match Unix.readdir dh with
    | exception End_of_file ->
        Unix.closedir dh;
        Ok ()
    | entry -> (
        if entry = "." || entry = ".." then loop ()
        else
          let src_path = Filename.concat src entry in
          let dst_path = Filename.concat dst entry in
          match (Unix.lstat src_path).st_kind with
          | S_REG ->
              (* TODO remove O(n^2) check *)
              if List.mem (Filename.basename src_path) filenames_to_copy then (
                match Filesystem.copy_file src_path dst_path with
                | Ok () -> loop ()
                | Error e ->
                    Unix.closedir dh;
                    Error e)
              else loop ()
          | S_DIR -> (
              match copy_dir src_path dst_path filenames_to_copy with
              | Ok () -> loop ()
              | Error e ->
                  Unix.closedir dh;
                  Error e)
          | _ ->
              (* skip symlinks/devices/etc. *)
              loop ())
  in
  loop ()

let set_input_arg (path : string) : unit =
  if Filesystem.is_directory path || Sys.file_exists path then input_arg := path
  else raise (Arg.Bad (Printf.sprintf "Invalid input file or folder: %s" path))

let set_transformation (t : string) : unit =
  match arg_to_transformation_kind t with
  | Ok Help ->
      print_endline "Available transformations:";
      print_endline (help_to_string transformations_help);
      exit 0
  | Ok arg -> transformation_arg := transformation_kind_to_string arg
  | Error err ->
      raise
        (Arg.Bad
           (err ^ "\nvalid transformations:\n"
           ^ help_to_string transformations_help))

let string_of_process_status = function
  | Unix.WEXITED code -> Printf.sprintf "Exited with code %d" code
  | Unix.WSIGNALED signal -> Printf.sprintf "Killed by signal %d" signal
  | Unix.WSTOPPED signal -> Printf.sprintf "Stopped by signal %d" signal

let remove_prefix (str : string) (prefix : string) =
  let prefix_len = String.length prefix in
  if String.length str >= prefix_len && String.sub str 0 prefix_len = prefix
  then String.sub str prefix_len (String.length str - prefix_len)
  else str

let speclist =
  [
    ("-v", Arg.Set verbose, "Enable debug output, incompatible with --quiet");
    ("-i", Arg.String set_input_arg, "Input folder or filename");
    ("-o", Arg.Set_string output_arg, "Output folder or filename");
    ("-t", Arg.String set_transformation, "Transformation to apply");
    ("--save-vo", Arg.Set save_vo, "Save a vo of the transformed file");
    ( "--quiet",
      Arg.Set quiet,
      "Silence progress output, incompatible with -v (verbose)" );
  ]

let usage_msg = "Usage: rocq-ditto [options]"

let warn_if_exists (dir_state : Filesystem.newDirState) =
  match dir_state with
  | AlreadyExists ->
      print_endline "Warning: output directory already exists: replacing files"
  | _ -> ()

let pp_level_lowercase (fmt : Format.formatter) (level : Logs.level) : unit =
  Format.pp_print_string fmt (Logs.level_to_string (Some level))

let pp_header_no_app fmt (level, _msg_header_opt) =
  match level with
  | Logs.App -> () (* App level: print nothing before the msg *)
  | _ -> Format.fprintf fmt "[%a] " pp_level_lowercase level

let transform_project () : (int, Error.t) result =
  print_newline ();
  let ( let* ) = Result.bind in

  let exec_name = Filename.basename Sys.argv.(0) in

  Arg.parse speclist
    (fun anon -> Printf.printf "Ignoring anonymous arg: %s\n" anon)
    usage_msg;
  let out = Format.std_formatter in
  let reporter =
    Logs_fmt.reporter ~pp_header:pp_header_no_app ~app:out ~dst:out ()
  in
  Logs.set_reporter reporter;

  if !verbose then Logs.set_level (Some Logs.Debug)
  else Logs.set_level (Some Logs.Info);

  let _ =
    match exec_name with
    | "coq-ditto" ->
        Logs.warn (fun m ->
            m
              "alias coq-ditto might disappear in the future, please use \
               rocq-ditto as the command name")
    | "rocq-ditto" -> ()
    | _ -> assert false
  in

  if !input_arg = "" then
    Error.string_to_or_error "Please provide an input folder or file"
  else if !output_arg = "" then
    Error.string_to_or_error "Please provide an output folder or filename"
  else if !transformation_arg = "" then
    Error.string_to_or_error "Please provide a transformation"
  else if !verbose && !quiet then
    Error.string_to_or_error
      "verbose option (-v) and quiet option (--quiet) are incompatible together"
  else
    match Filesystem.get_pathkind !input_arg with
    | File -> (
        if Filesystem.is_directory !output_arg then
          Error.string_to_or_error
            "Please provide a filename as output when providing a file as input"
        else
          let coqproject_opt =
            Compile.find_coqproject_dir_and_file !input_arg
          in

          let input_dir =
            Option.map (fun (dir, _) -> dir) coqproject_opt
            |> Option.default (Filename.dirname !input_arg)
          in

          print_endline ("input_dir: " ^ input_dir);
          let env =
            Array.append (Unix.environment ())
              [|
                "DITTO_TRANSFORMATION=" ^ !transformation_arg;
                "OUTPUT_FILENAME=" ^ !output_arg;
                "DEBUG_LEVEL=" ^ string_of_bool !verbose;
                "SAVE_VO=" ^ string_of_bool !save_vo;
                "QUIET=" ^ string_of_bool !quiet;
              |]
          in

          let prog = "fcc" in
          let args =
            [|
              prog; "--root=" ^ input_dir; "--plugin=ditto-plugin"; !input_arg;
            |]
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
        let coqproject_opt = Compile.find_coqproject_dir_and_file !input_arg in
        match coqproject_opt with
        | Some (coqproject_dir, coqproject_file) ->
            let open CoqProject_file in
            let coqproject_path =
              Filename.concat coqproject_dir coqproject_file
            in
            let p =
              CoqProject_file.read_project_file
                ~warning_fn:(fun _ -> ())
                coqproject_path
            in

            let files = List.map (fun x -> x.thing) p.files in
            let filenames = List.map Filename.basename files in
            let* dep_files = Compile.coqproject_sorted_files coqproject_path in
            let* new_dir_state = Filesystem.make_dir !output_arg in
            warn_if_exists new_dir_state;
            let* _ = copy_dir !input_arg !output_arg filenames in

            let* _ =
              Filesystem.copy_file coqproject_path
                (Filename.concat !output_arg coqproject_file)
            in

            let env =
              Array.append (Unix.environment ())
                [|
                  "DITTO_TRANSFORMATION=" ^ !transformation_arg;
                  "DEBUG_LEVEL=" ^ string_of_bool !verbose;
                  "SAVE_VO=" ^ string_of_bool !save_vo;
                  "QUIET=" ^ string_of_bool !quiet;
                |]
            in

            let prog = "fcc" in
            let args =
              [| prog; "--root=" ^ !output_arg; "--plugin=ditto-plugin" |]
            in

            let transformations_status =
              List.fold_left
                (fun err_acc x ->
                  match err_acc with
                  | Unix.WEXITED 0, _ ->
                      let rel_path = remove_prefix x !input_arg in

                      let curr_path = Filename.concat !output_arg rel_path in

                      let curr_args = Array.append args [| curr_path |] in
                      let curr_env =
                        Array.append env [| "OUTPUT_FILENAME=" ^ curr_path |]
                      in

                      let pid =
                        Unix.create_process_env prog curr_args curr_env
                          Unix.stdin Unix.stdout Unix.stderr
                      in
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
            else Ok 0
        | None ->
            prerr_endline
              (Printf.sprintf "No _CoqProject or _RocqProject file found in %s"
                 !input_arg);
            exit 1)

let () =
  match transform_project () with
  | Ok res -> exit res
  | Error err ->
      prerr_endline (Error.to_string_hum err);
      exit 1
