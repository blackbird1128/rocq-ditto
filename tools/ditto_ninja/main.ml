open Ditto

type cli_options = {
  path : string;
  output_folder : string;
  input_file_list : string option;
  output_file_map : string option;
  ditto_flags : string;
}

type resolved_options = {
  project : Project.t;
  selected_files : string list;
  outputs : (string * string) list; (* project input path, output path *)
  ditto_flags : string;
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

let read_output_file_map (map_path : string) :
    ((string * string) list, Error.t) result =
  let ( let* ) = Result.bind in
  let* lines = Filesystem.read_nonempty_lines map_path in
  let rec loop acc = function
    | [] -> Ok (List.rev acc)
    | line :: rest -> (
        match String_utils.split_words line with
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

let resolve_outputs ~(project_dir : string) ~(output_folder : string)
    ~(project_files : string list) ~(depfiles : string list)
    (output_file_map : (string * string) list) :
    ((string * string) list, Error.t) result =
  let unknown_inputs =
    output_file_map |> List.map fst
    |> List.filter (fun file -> not (List.mem file project_files))
  in
  if unknown_inputs <> [] then
    Error.format_to_or_error "Unknown input file(s) in output file map: %s"
      (String.concat ", " unknown_inputs)
  else
    let seen_outputs = Hashtbl.create 16 in
    let rec loop acc = function
      | [] -> Ok (List.rev acc)
      | file :: rest -> (
          let output_path =
            mapped_output_path ~project_dir ~output_folder ~output_file_map file
          in
          let normalized =
            Filesystem.normalize_path ~containing_dir:project_dir file
          in
          match Hashtbl.find_opt seen_outputs output_path with
          | None ->
              Hashtbl.add seen_outputs output_path normalized;
              loop ((file, output_path) :: acc) rest
          | Some previous ->
              Error.format_to_or_error
                "Multiple input files map to the same output path %S: %S and %S"
                output_path previous normalized)
    in
    loop [] depfiles

let coqproject_to_ninja_file (opts : resolved_options) :
    (Ninja.t, Error.t) result =
  let ( let* ) = Result.bind in

  let ditto_var = Ninja.variable "ditto" "rocq-ditto" in
  let ditto_flags_var = Ninja.variable "dittoflags" opts.ditto_flags in
  let ditto_rule = get_ninja_rule () in

  let* depgraph = Compile.coqproject_to_dep_graph opts.project in
  let depsgraph_seq = Dependency_graph.to_seq depgraph |> List.of_seq in

  let builds =
    List.concat_map
      (fun (file, neighbors) ->
        let filepath = file |> Ninja.Path.v in
        let output_filepath = List.assoc file opts.outputs |> Ninja.Path.v in
        let neighbors_paths =
          List.map
            (fun file -> List.assoc file opts.outputs |> Ninja.Path.v)
            neighbors
        in

        let normalized_input =
          Filesystem.normalize_path
            ~containing_dir:(Project.directory opts.project)
            file
        in

        if List.mem normalized_input opts.selected_files then
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

  let all_files =
    List.map (fun (_, output) -> Ninja.Path.v output) opts.outputs
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

let output_ditto_ninja_of_coqproject (opts : resolved_options) :
    (unit, Error.t) result =
  let ( let* ) = Result.bind in

  let* ninja_file = coqproject_to_ninja_file opts in
  Format.printf "%a\n%!" Ninja.pp ninja_file;
  Ok ()

let resolve_selected_files ~(project_files : string list)
    (input_file_list : string option) : (string list, Error.t) result =
  let ( let* ) = Result.bind in
  match input_file_list with
  | None -> Ok project_files
  | Some file_list_path -> (
      let* files = Filesystem.read_nonempty_lines file_list_path in
      match files with
      | [] ->
          Error.string_to_or_error
            "Please provide a non-empty file list when using --input-file-list"
      | files ->
          let unknown_inputs =
            List.filter (fun file -> not (List.mem file project_files)) files
          in
          if unknown_inputs = [] then Ok files
          else
            Error.format_to_or_error
              "Unknown input file(s) in --input-file-list: %s"
              (String.concat ", " unknown_inputs))

let resolve_options (opts : cli_options) : (resolved_options, Error.t) result =
  let ( let* ) = Result.bind in

  let* output_folder =
    if String.length opts.output_folder > 0 then Ok opts.output_folder
    else Error.string_to_or_error "Please provide a non-empty output folder"
  in

  let* project = Project.resolve_project_path opts.path in
  let project_dir = Project.directory project in
  let* depfiles = Compile.coqproject_sorted_files project in
  let project_depfiles =
    List.map
      (Filesystem.normalize_path ~containing_dir:(Project.directory project))
      depfiles
  in

  let* selected_files =
    resolve_selected_files ~project_files:project_depfiles opts.input_file_list
  in

  let* raw_output_file_map =
    match opts.output_file_map with
    | None -> Ok []
    | Some map_path -> read_output_file_map map_path
  in

  let* outputs =
    resolve_outputs ~project_dir ~output_folder ~project_files:project_depfiles
      ~depfiles raw_output_file_map
  in

  Ok { project; selected_files; outputs; ditto_flags = opts.ditto_flags }

let parse_args () : (cli_options, Error.t) result =
  let path = ref None in
  let output_folder = ref None in
  let ditto_flags = ref "" in
  let input_file_list = ref None in
  let output_file_map = ref None in

  let usage_msg =
    Printf.sprintf "Usage: %s [options] <path>" (Filename.basename Sys.argv.(0))
  in
  let specs =
    [
      ( "--output-folder",
        Arg.String (fun folder -> output_folder := Some folder),
        "Set the output folder of the ninja file" );
      ( "--input-file-list",
        Arg.String (fun path -> input_file_list := Some path),
        "Restrict file transformed by rocq-ditto to project-relative paths \
         listed in this file, one per line" );
      ( "--output-file-map",
        Arg.String (fun path -> output_file_map := Some path),
        "Rename selected outputs using a file of project-relative <input> \
         <output> pairs, one per line" );
      ( "--ditto-flags",
        Arg.Set_string ditto_flags,
        "The ditto flags to use for each invocation, empty by default" );
    ]
  in
  let set_path arg =
    match !path with
    | None -> path := Some arg
    | Some _ -> raise (Arg.Bad "Please provide exactly one path")
  in
  try
    Arg.parse specs set_path usage_msg;
    match (!path, !output_folder) with
    | Some path, Some output_folder ->
        Ok
          {
            path;
            output_folder;
            input_file_list = !input_file_list;
            output_file_map = !output_file_map;
            ditto_flags = !ditto_flags;
          }
    | None, _ -> Error.string_to_or_error "Please provide a path"
    | _, None -> Error.string_to_or_error "Please provide --output-folder"
  with
  | Arg.Bad msg -> Error.string_to_or_error msg
  | Arg.Help msg ->
      print_string msg;
      exit 0

let get_project_ninja () : (unit, Error.t) result =
  let ( let* ) = Result.bind in
  let* args = parse_args () in

  let* resolved_options = resolve_options args in

  output_ditto_ninja_of_coqproject resolved_options

let main =
  match get_project_ninja () with
  | Ok _ -> exit 0
  | Error err ->
      Printf.eprintf "%s\n%!" (Error.to_string_hum err);
      exit 1

let () = main
