open Ditto

let input_folder = ref ""
let output_folder = ref ""
let verbose = ref false

let is_directory (path : string) : bool =
  try
    let stats = Unix.stat path in
    stats.Unix.st_kind = Unix.S_DIR
  with Unix.Unix_error _ -> false

let copy_file src dst : (unit, string) result =
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
  | Sys_error msg -> Error msg
  | e -> Error (Printexc.to_string e)

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

let set_input_folder (path : string) =
  if is_directory path then input_folder := path
  else raise (Arg.Bad (Printf.sprintf "Invalid input folder: %s" path))

let speclist =
  [
    ("-v", Arg.Set verbose, "Enable verbose output");
    ("-i", Arg.String set_input_folder, "Input folder");
    ("-o", Arg.Set_string output_folder, "Output folder");
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

  if !input_folder = "" then
    Error.string_to_or_error_err "Please provide an input folder"
  else if !output_folder = "" then
    Error.string_to_or_error_err "Please provide an output folder"
  else
    let coqproject_opt = Compile.find_coqproject !input_folder in
    match coqproject_opt with
    | Some coqproject ->
        let open CoqProject_file in
        let coqproject_file = coqproject ^ "_CoqProject" in
        print_endline ("coq project file: " ^ coqproject_file);
        let p =
          CoqProject_file.read_project_file
            ~warning_fn:(fun _ -> ())
            coqproject_file
        in
        let files = List.map (fun x -> x.thing) p.files in
        let filenames = List.map Filename.basename files in
        List.iter print_endline files;
        print_endline "---------------------------";
        let* dep_files = Compile.coqproject_sorted_files coqproject_file in

        let* new_dir_state = make_dir !output_folder in
        warn_if_exists new_dir_state;

        exit 0
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
