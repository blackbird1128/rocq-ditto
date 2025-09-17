open Ditto
open Ditto.Diagnostic_utils
open Ditto.Proof

type transformation_kind =
  | Help
  | MakeIntrosExplicit
  | TurnIntoOneliner
  | ReplaceAutoWithSteps
  | CompressIntro
  | IdTransformation

let input_folder = ref ""
let output_folder = ref ""
let transformation_arg = ref ""
let verbose = ref false

let arg_to_transformation_kind (arg : string) :
    (transformation_kind, string) result =
  let normalized = String.lowercase_ascii arg in
  if normalized = "help" then Ok Help
  else if normalized = "make_intros_explicit" then Ok MakeIntrosExplicit
  else if normalized = "turn_into_one_liner" then Ok TurnIntoOneliner
  else if normalized = "replace_auto_with_steps" then Ok ReplaceAutoWithSteps
  else if normalized = "compress_intro" then Ok CompressIntro
  else if normalized = "id_transformation" then Ok IdTransformation
  else
    Error
      ("transformation " ^ arg ^ "wasn't recognized as a valid transformation")

let transformation_kind_to_string (kind : transformation_kind) : string =
  match kind with
  | Help -> "HELP"
  | MakeIntrosExplicit -> "MAKE_INTROS_EXPLICIT"
  | TurnIntoOneliner -> "TURN_INTO_ONELINER"
  | ReplaceAutoWithSteps -> "REPLACE_AUTO_WITH_STEPS"
  | CompressIntro -> "COMPRESS_INTROS"
  | IdTransformation -> "ID_TRANSFORMATION"

let is_directory (path : string) : bool =
  try
    let stats = Unix.stat path in
    stats.Unix.st_kind = Unix.S_DIR
  with Unix.Unix_error _ -> false

let copy_file (src : string) (dst : string) : (unit, Error.t) result =
  let buffer_size = 8192 in
  let buffer = Bytes.create buffer_size in
  try
    let ic = open_in_bin src in
    let oc = open_out_bin dst in
    let rec loop () =
      match input ic buffer 0 buffer_size with
      | 0 -> ()
      | n ->
          output oc buffer 0 n;
          loop ()
    in
    loop ();
    close_in ic;
    close_out oc;
    Ok ()
  with
  | Sys_error msg -> Error.string_to_or_error_err msg
  | e -> Error.string_to_or_error_err (Printexc.to_string e)

type newDirState = AlreadyExists | Created

let make_dir dir_name : (newDirState, Error.t) result =
  let perm = 0o755 in
  if Sys.file_exists dir_name then Ok AlreadyExists
  else
    try
      Unix.mkdir dir_name perm;
      Ok Created
    with Unix.Unix_error (err, _, _) ->
      Error.string_to_or_error_err (Unix.error_message err)

let set_input_folder (path : string) : unit =
  if is_directory path then input_folder := path
  else raise (Arg.Bad (Printf.sprintf "Invalid input folder: %s" path))

let set_transformation (t : string) : unit =
  match arg_to_transformation_kind t with
  | Ok arg -> transformation_arg := transformation_kind_to_string arg
  | Error err -> raise (Arg.Bad err)

let string_of_process_status = function
  | Unix.WEXITED code -> Printf.sprintf "Exited with code %d" code
  | Unix.WSIGNALED signal -> Printf.sprintf "Killed by signal %d" signal
  | Unix.WSTOPPED signal -> Printf.sprintf "Stopped by signal %d" signal

(* Example usage *)
let () =
  let status = Unix.system "ls" in
  print_endline (string_of_process_status status)

let speclist =
  [
    ("-v", Arg.Set verbose, "Enable verbose output");
    ("-i", Arg.String set_input_folder, "Input folder");
    ("-o", Arg.Set_string output_folder, "Output folder");
    ("-t", Arg.String set_transformation, "Transformation to apply");
  ]

let usage_msg = "Usage: project_ditto [options]"

let warn_if_exists (dir_state : newDirState) =
  match dir_state with
  | AlreadyExists ->
      print_endline "Warning: output directory already exists: replacing files"
  | _ -> ()

let transform_project () : (int, Error.t) result =
  print_newline ();
  let ( let* ) = Result.bind in
  Arg.parse speclist
    (fun anon -> Printf.printf "Ignoring anonymous arg: %s\n" anon)
    usage_msg;
  let dev_null = Unix.openfile "/dev/null" [ Unix.O_WRONLY ] 0o666 in

  if !input_folder = "" then
    Error.string_to_or_error_err "Please provide an input folder"
  else if !output_folder = "" then
    Error.string_to_or_error_err "Please provide an output folder"
  else if !transformation_arg = "" then
    Error.string_to_or_error_err "Please provide a transformation"
  else
    let coqproject_opt = Compile.find_coqproject !input_folder in
    match coqproject_opt with
    | Some coqproject_folder ->
        let open CoqProject_file in
        let coqproject_file = coqproject_folder ^ "_CoqProject" in
        print_endline ("coq project file: " ^ coqproject_file);
        let p =
          CoqProject_file.read_project_file
            ~warning_fn:(fun _ -> ())
            coqproject_file
        in
        let files = List.map (fun x -> x.thing) p.files in
        let filenames = List.map Filename.basename files in
        print_endline "---------------------------";
        let* dep_files = Compile.coqproject_sorted_files coqproject_file in
        let dep_filenames = List.map Filename.basename dep_files in
        List.iter (fun x -> print_endline ("dep: " ^ x)) dep_files;
        let* new_dir_state = make_dir !output_folder in
        warn_if_exists new_dir_state;

        let copy_file_status =
          List.mapi
            (fun i x ->
              copy_file x
                (Filename.concat !output_folder (List.nth filenames i)))
            files
        in
        let opt_err = List.find_opt Result.is_error copy_file_status in
        if Option.has_some opt_err then
          let err = Option.get opt_err in
          let err_message = Result.get_error err in
          Error err_message
        else
          let* coq_project_copy =
            copy_file coqproject_file
              (Filename.concat !output_folder "_CoqProject")
          in

          let env =
            Array.append (Unix.environment ())
              [|
                "DITTO_TRANSFORMATION=make_intros_explicit"; "FILE_POSTFIX=.v";
              |]
          in

          let prog = "fcc" in
          let args =
            [| prog; "--root=" ^ !output_folder; "--plugin=ditto-plugin" |]
          in

          let transformations_status =
            List.map
              (fun x ->
                let curr_args =
                  Array.append args [| Filename.concat !output_folder x |]
                in

                let pid =
                  Unix.create_process_env prog curr_args env Unix.stdin
                    Unix.stdout Unix.stderr
                in
                let _, status = Unix.waitpid [] pid in
                (status, x))
              dep_filenames
          in
          let opt_err_transformation =
            List.find_opt
              (fun (status, x) ->
                match status with Unix.WEXITED 0 -> false | _ -> true)
              transformations_status
          in
          if Option.has_some opt_err_transformation then
            let err = Option.get opt_err_transformation in
            Error.string_to_or_error_err
              (string_of_process_status (fst err) ^ " filename " ^ snd err)
          else Ok 0
    | None ->
        prerr_endline
          (Printf.sprintf "No CoqProject_ file found in %s" !input_folder);
        exit 1

let () =
  match transform_project () with
  | Ok res -> exit res
  | Error err ->
      prerr_endline (Error.to_string_hum err);
      exit 1
