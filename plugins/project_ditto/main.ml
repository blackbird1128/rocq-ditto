open Ditto

let input_folder = ref ""
let verbose = ref false

let is_directory (path : string) : bool =
  try
    let stats = Unix.stat path in
    stats.Unix.st_kind = Unix.S_DIR
  with Unix.Unix_error _ -> false

let set_input_folder path =
  if is_directory path then input_folder := path
  else raise (Arg.Bad (Printf.sprintf "Invalid input folder: %s" path))

let speclist =
  [
    ("-v", Arg.Set verbose, "Enable verbose output");
    ("-i", Arg.String set_input_folder, "Input folder");
  ]

let usage_msg = "Usage: myprog [options]"

let () =
  let ( let* ) = Option.bind in
  Arg.parse speclist
    (fun anon -> Printf.printf "Ignoring anonymous arg: %s\n" anon)
    usage_msg;

  if !input_folder = "" then (
    prerr_endline "Please provide an input folder";

    exit 1)
  else
    let coqproject_opt = Compile.find_coqproject !input_folder in
    match coqproject_opt with
    | Some coqproject ->
        
    | None ->
        prerr_endline
          (Printf.sprintf "No CoqProject_ file found in %s" !input_folder);
        exit 1
