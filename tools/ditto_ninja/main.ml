open Ditto

let get_ninja_rule () =
  let rule =
    Ninja.make_rule ~name:"ditto"
      ~command:(Printf.sprintf "$ditto -i $in -o $out $dittoflags")
      ()
  in
  Ninja.rule rule

type cli_options = {
  path : string;
  output_folder : string;
  default_prefixes : string list;
  default_file_list : string option;
  output_file_map : string option;
}

let relocate (input_folder : string) (output_folder : string)
    (filename : string) =
  let rel_file_path = String_utils.remove_prefix filename input_folder in
  let rel_file_without_lead_slash =
    String_utils.remove_prefix rel_file_path "/"
  in
  Filename.concat output_folder rel_file_without_lead_slash

let normalize_path ~(project_dir : string) (path : string) : string =
  let with_sep =
    if Filename.check_suffix project_dir Filename.dir_sep then project_dir
    else project_dir ^ Filename.dir_sep
  in
  (path |> fun x -> String_utils.remove_prefix x with_sep) |> fun x ->
  String_utils.remove_prefix x "/"

let include_in_default ~(project_dir : string) ~(default_prefixes : string list)
    (file : string) : bool =
  match default_prefixes with
  | [] -> true
  | prefixes ->
      let normalized = normalize_path ~project_dir file in
      List.exists (fun prefix -> String.starts_with ~prefix normalized) prefixes

let read_nonempty_lines (path : string) : (string list, Error.t) result =
  try
    let ic = open_in_bin path in
    let len = in_channel_length ic in
    let contents = really_input_string ic len in
    close_in ic;
    contents |> String.split_on_char '\n'
    |> List.map String.trim
    |> List.filter (fun line -> line <> "" && not (String.starts_with ~prefix:"#" line))
    |> fun lines -> Ok lines
  with
  | Sys_error msg -> Error.string_to_or_error msg

let split_words (line : string) : string list =
  let rec skip_spaces i =
    if i < String.length line then
      match line.[i] with
      | ' ' | '\t' -> skip_spaces (i + 1)
      | _ -> i
    else i
  in
  let rec take_word i j =
    if j < String.length line then
      match line.[j] with
      | ' ' | '\t' -> String.sub line i (j - i), j
      | _ -> take_word i (j + 1)
    else String.sub line i (j - i), j
  in
  let rec loop i acc =
    let i = skip_spaces i in
    if i >= String.length line then List.rev acc
    else
      let word, j = take_word i i in
      loop j (word :: acc)
  in
  loop 0 []

let read_default_file_list (file_list_path : string) :
    (string list, Error.t) result =
  read_nonempty_lines file_list_path

let read_output_file_map (map_path : string) :
    ((string * string) list, Error.t) result =
  let ( let* ) = Result.bind in
  let* lines = read_nonempty_lines map_path in
  let rec loop acc = function
    | [] -> Ok (List.rev acc)
    | line :: rest -> (
        match split_words line with
        | [ input_path; output_path ] ->
            if List.mem_assoc input_path acc then
              Error.format_to_or_error
                "Duplicate input in output file map: %S" input_path
            else loop ((input_path, output_path) :: acc) rest
        | _ ->
            Error.format_to_or_error
              "Invalid line in output file map: %S. Expected: <input> <output>"
              line)
  in
  loop [] lines

let mapped_output_path ~(project_dir : string) ~(output_folder : string)
    ~(output_file_map : (string * string) list) (file : string) : string =
  let normalized = normalize_path ~project_dir file in
  match List.assoc_opt normalized output_file_map with
  | Some mapped_path -> Filename.concat output_folder mapped_path
  | None -> relocate project_dir output_folder file

let validate_unique_outputs ~(project_dir : string) ~(output_folder : string)
    ~(output_file_map : (string * string) list) (files : string list) :
    (unit, Error.t) result =
  let outputs = Hashtbl.create 16 in
  let rec loop = function
    | [] -> Ok ()
    | file :: rest ->
        let output_path =
          mapped_output_path ~project_dir ~output_folder ~output_file_map file
        in
        let normalized = normalize_path ~project_dir file in
        (match Hashtbl.find_opt outputs output_path with
        | None ->
            Hashtbl.add outputs output_path normalized;
            loop rest
        | Some previous ->
            Error.format_to_or_error
              "Multiple input files map to the same output path %S: %S and %S"
              output_path previous normalized)
  in
  loop files

let coqproject_to_ninja_file (coqproject_path : string) (output_folder : string)
    ~(default_prefixes : string list) ~(default_file_list : string option)
    ~(output_file_map : string option)
    : (Ninja.t, Error.t) result =
  let ( let* ) = Result.bind in

  let project_dir = Filename.dirname coqproject_path in
  let* default_files =
    match default_file_list with
    | None -> Ok None
    | Some file_list_path ->
        let* files = read_default_file_list file_list_path in
        Ok (Some files)
  in
  let* output_file_map =
    match output_file_map with
    | None -> Ok []
    | Some map_path -> read_output_file_map map_path
  in

  let* depgraph = Compile.coqproject_to_dep_graph coqproject_path in
  let* depfiles = Compile.coqproject_sorted_files coqproject_path in
  let project_depfiles =
    List.map (normalize_path ~project_dir) depfiles
  in
  let* () =
    match default_files with
    | None -> Ok ()
    | Some files ->
        let unknown_files =
          List.filter (fun file -> not (List.mem file project_depfiles)) files
        in
        if unknown_files = [] then Ok ()
        else
          Error.format_to_or_error
            "Unknown file(s) in default file list: %s"
            (String.concat ", " unknown_files)
  in
  let* () =
    let unknown_inputs =
      output_file_map
      |> List.map fst
      |> List.filter (fun file -> not (List.mem file project_depfiles))
    in
    if unknown_inputs = [] then Ok ()
    else
      Error.format_to_or_error
        "Unknown input file(s) in output file map: %s"
        (String.concat ", " unknown_inputs)
  in
  let* () =
    validate_unique_outputs ~project_dir ~output_folder ~output_file_map
      depfiles
  in

  let detached = List.filter (fun x -> not (Hashtbl.mem depgraph x)) depfiles in

  let _pad_depgraph = List.iter (fun x -> Hashtbl.add depgraph x []) detached in

  let ditto_var =
    Ninja.variable "ditto" "dune exec --profile=release rocq-ditto --"
  in

  let ditto_flags_var = Ninja.variable "dittoflags" "" in

  let rule = get_ninja_rule () in

  let depsgraph_seq = Hashtbl.to_seq depgraph |> List.of_seq in

  let builds =
    List.map
      (fun (file, neighbors) ->
        let filepath = file |> Ninja.Path.v in
        let output_filepath =
          mapped_output_path ~project_dir ~output_folder ~output_file_map file
          |> Ninja.Path.v
        in
        let neighbors_paths =
          List.map
            (fun file ->
              mapped_output_path ~project_dir ~output_folder ~output_file_map
                file
              |> Ninja.Path.v)
            neighbors
        in
        Ninja.make_build ~inputs:[ filepath ] ~outputs:[ output_filepath ]
          ~implicit:neighbors_paths ~rule:"ditto" ())
      depsgraph_seq
    |> List.map Ninja.build |> Ninja.concat
  in
  let default_paths =
    List.map
      (fun file ->
        mapped_output_path ~project_dir ~output_folder ~output_file_map file
        |> Ninja.Path.v)
      (List.filter
         (fun file ->
           let normalized = normalize_path ~project_dir file in
           match default_files with
           | Some files -> List.mem normalized files
           | None ->
               include_in_default ~project_dir ~default_prefixes file)
         depfiles)
  in
  let defaults = Ninja.default default_paths in

  Ok (Ninja.concat [ ditto_flags_var; ditto_var; rule; builds; defaults ])

let output_ditto_ninja_of_coqproject (project_dir : string)
    (project_filename : string) (output_folder : string)
    ~(default_prefixes : string list) ~(default_file_list : string option)
    ~(output_file_map : string option) :
    (unit, Error.t) result =
  let ( let* ) = Result.bind in
  let project_path = Filename.concat project_dir project_filename in
  let* ninja_file =
    coqproject_to_ninja_file project_path output_folder ~default_prefixes
      ~default_file_list ~output_file_map
  in
  Format.printf "%a\n%!" Ninja.pp ninja_file;
  Ok ()

let parse_args () : (cli_options, Error.t) result =
  let path = ref None in
  let output_folder = ref "" in
  let default_prefixes = ref [] in
  let default_file_list = ref None in
  let output_file_map = ref None in

  let usage_msg =
    Printf.sprintf "Usage: %s [options] <path>" (Filename.basename Sys.argv.(0))
  in
  let specs =
    [
      ( "--output-folder",
        Arg.Set_string output_folder,
        "Set the output folder of the ninja file" );
      ( "--default-prefix",
        Arg.String (fun prefix -> default_prefixes := prefix :: !default_prefixes),
        "Restrict files listed in the default ninja target to project-relative \
         paths with this prefix (repeatable)" );
      ( "--default-file-list",
        Arg.String (fun path -> default_file_list := Some path),
        "Restrict files listed in the default ninja target to project-relative \
         paths listed in this file, one per line" );
      ( "--output-file-map",
        Arg.String (fun path -> output_file_map := Some path),
        "Rename selected outputs using a file of project-relative \
         <input> <output> pairs, one per line" );
    ]
  in
  let set_path arg =
    match !path with
    | None -> path := Some arg
    | Some _ -> raise (Arg.Bad "Please provide exactly one path")
  in
  try
    Arg.parse specs set_path usage_msg;
    match !path with
    | Some path ->
        Ok
          {
            path;
            output_folder = !output_folder;
            default_prefixes = List.rev !default_prefixes;
            default_file_list = !default_file_list;
            output_file_map = !output_file_map;
          }
    | None -> Error.string_to_or_error "Please provide a path"
  with
  | Arg.Bad msg -> Error.string_to_or_error msg
  | Arg.Help msg ->
      print_string msg;
      exit 0

let get_project_ninja () : (unit, Error.t) result =
  let ( let* ) = Result.bind in
  let* { path; output_folder; default_prefixes; default_file_list; output_file_map }
      =
    parse_args ()
  in

  if output_folder = "" then
    Error.string_to_or_error "Please provide an output folder"
  else if default_file_list <> None && default_prefixes <> [] then
    Error.string_to_or_error
      "Please provide at most one of --default-prefix and --default-file-list"
  else if not (Sys.file_exists path) then
    Error.string_to_or_error
      "Please provide a path to an existing file or directory"
  else if Filesystem.is_directory path then
    match Compile.find_coqproject_dir_and_file path with
    | None ->
        Error.string_to_or_error
          "No _CoqProject or _RocqProject found in the directory provided"
    | Some (dir, filename) ->
        output_ditto_ninja_of_coqproject dir filename output_folder
          ~default_prefixes ~default_file_list ~output_file_map
  else if
    Filename.basename path <> "_CoqProject"
    && Filename.basename path <> "_RocqProject"
  then
    Error.string_to_or_error
      "Please provide a path to a directory or to a _CoqProject or \
       _RocqProject file"
  else
    let path_dir = Filename.dirname path in
    let path_name = Filename.basename path in
    output_ditto_ninja_of_coqproject path_dir path_name output_folder
      ~default_prefixes ~default_file_list ~output_file_map

let main =
  match get_project_ninja () with
  | Ok _ -> exit 0
  | Error err ->
      Printf.eprintf "%s\n%!" (Error.to_string_hum err);
      exit 1

let () = main
