open Ditto

type cli_options = {
  path : string;
  output_folder : string;
  default_prefixes : string list;
  transformed_file_list : string option;
  output_file_map : string option;
}

let get_ninja_rule () =
  let rule =
    Ninja.make_rule ~name:"ditto"
      ~command:(Printf.sprintf "$ditto -i $in -o $out $dittoflags")
      ()
  in
  Ninja.rule rule

let get_id_ninja_rule () =
  let rule = Ninja.make_rule ~name:"id" ~command:"cp $in $out" () in
  Ninja.rule rule

let split_words (line : string) : string list =
  let rec skip_spaces i =
    if i < String.length line then
      match line.[i] with ' ' | '\t' -> skip_spaces (i + 1) | _ -> i
    else i
  in
  let rec take_word i j =
    if j < String.length line then
      match line.[j] with
      | ' ' | '\t' -> (String.sub line i (j - i), j)
      | _ -> take_word i (j + 1)
    else (String.sub line i (j - i), j)
  in
  let rec loop i acc =
    let i = skip_spaces i in
    if i >= String.length line then List.rev acc
    else
      let word, j = take_word i i in
      loop j (word :: acc)
  in
  loop 0 []

let read_output_file_map (map_path : string) :
    ((string * string) list, Error.t) result =
  let ( let* ) = Result.bind in
  let* lines = Filesystem.read_nonempty_lines map_path in
  let rec loop acc = function
    | [] -> Ok (List.rev acc)
    | line :: rest -> (
        match split_words line with
        | [ input_path; output_path ] ->
            if List.mem_assoc input_path acc then
              Error.format_to_or_error "Duplicate input in output file map: %S"
                input_path
            else loop ((input_path, output_path) :: acc) rest
        | _ ->
            Error.format_to_or_error
              "Invalid line in output file map: %S. Expected: <input> <output>"
              line)
  in
  loop [] lines

let mapped_output_path ~(project_dir : string) ~(output_folder : string)
    ~(output_file_map : (string * string) list) (file : string) : string =
  let normalized = Filesystem.normalize_path ~containing_dir:project_dir file in
  match List.assoc_opt normalized output_file_map with
  | Some mapped_path -> Filename.concat output_folder mapped_path
  | None -> Filesystem.relocate_path project_dir output_folder file

let validate_unique_outputs ~(project_dir : string) ~(output_folder : string)
    ~(output_file_map : (string * string) list) (files : string list) :
    (unit, Error.t) result =
  let outputs = Hashtbl.create 16 in
  let rec loop = function
    | [] -> Ok ()
    | file :: rest -> (
        let output_path =
          mapped_output_path ~project_dir ~output_folder ~output_file_map file
        in
        let normalized =
          Filesystem.normalize_path ~containing_dir:project_dir file
        in
        match Hashtbl.find_opt outputs output_path with
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
    ~(transformed_file_list : string option) ~(output_file_map : string option)
    : (Ninja.t, Error.t) result =
  let ( let* ) = Result.bind in

  let project_dir = Filename.dirname coqproject_path in
  let* transformed_files =
    match transformed_file_list with
    | None -> Ok []
    | Some file_list_path ->
        let* files = Filesystem.read_nonempty_lines file_list_path in
        Ok files
  in

  let* output_file_map =
    match output_file_map with
    | None -> Ok []
    | Some map_path -> read_output_file_map map_path
  in

  let* depgraph = Compile.coqproject_to_dep_graph coqproject_path in
  let* depfiles = Compile.coqproject_sorted_files coqproject_path in
  let project_depfiles =
    List.map (Filesystem.normalize_path ~containing_dir:project_dir) depfiles
  in

  let* () =
    let unknown_inputs =
      output_file_map |> List.map fst
      |> List.filter (fun file -> not (List.mem file project_depfiles))
    in
    if unknown_inputs = [] then Ok ()
    else
      Error.format_to_or_error "Unknown input file(s) in output file map: %s"
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

  let ditto_rule = get_ninja_rule () in

  let depsgraph_seq = Hashtbl.to_seq depgraph |> List.of_seq in

  let builds =
    List.concat_map
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
        (* let normalized = *)
        (*   Filesystem.normalize_path ~containing_dir:project_dir file *)
        (* in *)

        let normalized_out =
          Filesystem.normalize_path ~containing_dir:output_folder
            (Ninja.Path.to_string output_filepath)
        in

        if transformed_files = [] || List.mem normalized_out transformed_files
        then
          [
            Ninja.make_build ~inputs:[ filepath ] ~outputs:[ output_filepath ]
              ~implicit:neighbors_paths ~rule:"ditto" ();
          ]
        else
          [
            Ninja.make_build ~inputs:[ filepath ] ~outputs:[ output_filepath ]
              ~implicit:neighbors_paths ~rule:"id" ();
          ])
      depsgraph_seq
    |> List.map Ninja.build |> Ninja.concat
  in

  (* let unmapped = *)
  (*   List.filter_map *)
  (*     (fun file -> *)
  (*       if not (List.mem_assoc file output_file_map) then *)
  (*         Some *)
  (*           (Ninja.Path.v *)
  (*              (Filesystem.relocate_path project_dir output_folder file)) *)
  (*       else None) *)
  (*     depfiles *)
  (* in *)
  let all_files =
    List.map
      (fun file ->
        mapped_output_path ~project_dir ~output_folder ~output_file_map file
        |> Ninja.Path.v)
      depfiles
  in

  let defaults = all_files |> Ninja.default in

  Ok
    (Ninja.concat
       [
         ditto_flags_var;
         ditto_var;
         get_id_ninja_rule ();
         ditto_rule;
         builds;
         defaults;
       ])

let output_ditto_ninja_of_coqproject (project_dir : string)
    (project_filename : string) (output_folder : string)
    ~(transformed_file_list : string option) ~(output_file_map : string option)
    : (unit, Error.t) result =
  let ( let* ) = Result.bind in
  let project_path = Filename.concat project_dir project_filename in
  let* ninja_file =
    coqproject_to_ninja_file project_path output_folder ~transformed_file_list
      ~output_file_map
  in
  Format.printf "%a\n%!" Ninja.pp ninja_file;
  Ok ()

let parse_args () : (cli_options, Error.t) result =
  let path = ref None in
  let output_folder = ref "" in
  let default_prefixes = ref [] in
  let transformed_file_list = ref None in
  let output_file_map = ref None in

  let usage_msg =
    Printf.sprintf "Usage: %s [options] <path>" (Filename.basename Sys.argv.(0))
  in
  let specs =
    [
      ( "--output-folder",
        Arg.Set_string output_folder,
        "Set the output folder of the ninja file" );
      ( "--transformed-file-list",
        Arg.String (fun path -> transformed_file_list := Some path),
        "Restrict files transformed by rocq-ditto to project-relative paths \
         listed in this file, one per line" );
      ( "--output-file-map",
        Arg.String (fun path -> output_file_map := Some path),
        "Rename selected outputs using a file of project-relative <input> \
         <output> pairs, one per line" );
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
            transformed_file_list = !transformed_file_list;
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
  let* {
         path;
         output_folder;
         default_prefixes;
         transformed_file_list;
         output_file_map;
       } =
    parse_args ()
  in

  if output_folder = "" then
    Error.string_to_or_error "Please provide an output folder"
  else if transformed_file_list <> None && default_prefixes <> [] then
    Error.string_to_or_error
      "Please provide at most one of --default-prefix and \
       --transformed-file-list"
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
          ~transformed_file_list ~output_file_map
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
      ~transformed_file_list ~output_file_map

let main =
  match get_project_ninja () with
  | Ok _ -> exit 0
  | Error err ->
      Printf.eprintf "%s\n%!" (Error.to_string_hum err);
      exit 1

let () = main
