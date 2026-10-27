open Ditto

type action_kind = Transform | Stats
type format_kind = Text | Json

type cli_options = {
  action : action_kind;
  path : string;
  output_folder : string;
  input_file_list : string option;
  output_file_map : string option;
  statistic : string option;
  format : format_kind option;
  ditto_flags : string;
}

type common_option = {
  project : Project.t;
  selected_files : string list;
  outputs : (string * string) list; (* project input path, output path *)
}

type resolved_options =
  | Transformation of { common : common_option; ditto_flags : string }
  | Statistics of {
      common : common_option;
      statistic : string;
      format : format_kind;
    }

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
    ~(output_file_map : (string * string) list) (file : string)
    (output_extension : string) : string =
  let normalized = Filesystem.normalize_path ~containing_dir:project_dir file in
  match List.assoc_opt normalized output_file_map with
  | Some mapped_path -> Filename.concat output_folder mapped_path
  | None ->
      let file_with_new_ext =
        Filename.remove_extension file ^ output_extension
      in
      Filesystem.relocate_path project_dir output_folder file_with_new_ext

let resolve_outputs ~(project_dir : string) ~(output_folder : string)
    ~(project_files : string list) ~(depfiles : string list)
    (output_file_map : (string * string) list) (output_extension : string) :
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
              output_extension
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

let generate_stats_ninja (opts : common_option) (statistic : string)
    (format : format_kind) : (Ninja.t, Error.t) result =
  let ditto_var = Ninja.variable "ditto" "rocq-ditto" in
  let statistic_var = Ninja.variable "statistic" statistic in
  let format_var =
    match format with
    | Text -> Ninja.variable "format" "text"
    | Json -> Ninja.variable "format" "json"
  in

  let ditto_rule =
    Ninja.make_rule ~name:"ditto"
      ~command:
        (Printf.sprintf "$ditto stats -i $in  -s $statistic -f $format > $out")
      ()
    |> Ninja.rule
  in

  let project_dir = Project.directory opts.project in
  let selected_outputs =
    List.filter
      (fun (file, _) ->
        List.mem
          (Filesystem.normalize_path ~containing_dir:project_dir file)
          opts.selected_files)
      opts.outputs
  in

  let builds =
    List.concat_map
      (fun (file_input, file_output) ->
        let file_input_path = file_input |> Ninja.Path.v in
        let file_output_path = file_output |> Ninja.Path.v in
        [
          Ninja.make_build ~inputs:[ file_input_path ]
            ~outputs:[ file_output_path ] ~rule:"ditto" ();
        ])
      selected_outputs
    |> List.map Ninja.build |> Ninja.concat
  in

  let all_selected_output_files =
    List.map (fun (_, output) -> Ninja.Path.v output) selected_outputs
  in

  let defaults = all_selected_output_files |> Ninja.default in

  Ok
    (Ninja.concat
       [ ditto_var; statistic_var; format_var; ditto_rule; builds; defaults ])

let generate_transform_ninja (opts : common_option) (ditto_flags : string) :
    (Ninja.t, Error.t) result =
  let ( let* ) = Result.bind in

  let ditto_var = Ninja.variable "ditto" "rocq-ditto" in
  let ditto_flags_var = Ninja.variable "dittoflags" ditto_flags in

  let ditto_rule =
    Ninja.make_rule ~name:"ditto"
      ~command:(Printf.sprintf "$ditto -i $in -o $out $dittoflags")
      ()
    |> Ninja.rule
  in

  let id_rule =
    Ninja.make_rule ~name:"id" ~command:"cp $in $out" () |> Ninja.rule
  in

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
       [ ditto_flags_var; ditto_var; id_rule; ditto_rule; builds; defaults ])

let coqproject_to_ninja_file (opts : resolved_options) :
    (Ninja.t, Error.t) result =
  match opts with
  | Transformation { common; ditto_flags } ->
      generate_transform_ninja common ditto_flags
  | Statistics { common; statistic; format } ->
      generate_stats_ninja common statistic format

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

  let* _ =
    match opts.action with
    | Transform ->
        if Option.has_some opts.statistic then
          Error.string_to_or_error
            "Cannot use --statistic with --action transform"
        else if Option.has_some opts.format then
          Error.string_to_or_error "Cannot use --format with --action transform"
        else Ok ()
    | Stats ->
        if String.length opts.ditto_flags > 0 then
          Error.string_to_or_error
            "Cannot use --ditto-flags with --action stats"
        else Ok ()
  in

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

  let format = Option.default Text opts.format in
  let output_extension =
    match opts.action with
    | Transform -> ".v"
    | Stats -> ( match format with Text -> ".txt" | Json -> ".json")
  in

  (* TODO: Report output-file-map entries for unselected files in stats mode. *)
  let output_depfiles =
    match opts.action with
    | Transform -> depfiles
    | Stats ->
        List.filter
          (fun file ->
            let normalized =
              Filesystem.normalize_path ~containing_dir:project_dir file
            in
            List.mem normalized selected_files)
          depfiles
  in

  let* outputs =
    resolve_outputs ~project_dir ~output_folder ~project_files:project_depfiles
      ~depfiles:output_depfiles raw_output_file_map output_extension
  in

  let common = { project; selected_files; outputs } in

  match opts.action with
  | Transform -> Ok (Transformation { common; ditto_flags = opts.ditto_flags })
  | Stats ->
      let* statistic =
        Option_utils.to_result opts.statistic
          ~none:
            (Error.string_to_or_error
               "--statistic must be provided when using --action stats")
      in
      Ok (Statistics { common; statistic; format })

let parse_args () : (cli_options, Error.t) result =
  let action = ref Transform in
  let format = ref None in
  let statistic = ref None in
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
      ( "--action",
        Arg.Symbol
          ( [ "transform"; "stats" ],
            fun str ->
              match str with
              | "transform" -> action := Transform
              | "stats" -> action := Stats
              | _ -> assert false ),
        " Generate transformation or statistics rules (default: transform)" );
      ( "--format",
        Arg.Symbol
          ( [ "text"; "json" ],
            fun str ->
              match str with
              | "text" -> format := Some Text
              | "json" -> format := Some Json
              | _ -> assert false ),
        " Statistics output format (default: text; stats only)" );
      ( "--output-folder",
        Arg.String (fun folder -> output_folder := Some folder),
        "Directory for generated output files (required)" );
      ( "--input-file-list",
        Arg.String (fun path -> input_file_list := Some path),
        "Select project-relative input files listed one per line; unlisted \
         files are copied in transform mode and omitted in stats mode" );
      ( "--output-file-map",
        Arg.String (fun path -> output_file_map := Some path),
        "Map project-relative <input> paths to <output> paths relative to the \
         output folder, one pair per line" );
      ( "--statistic",
        Arg.String (fun stat -> statistic := Some stat),
        "Statistic kind passed to rocq-ditto stats (required for --action stats)"
      );
      ( "--ditto-flags",
        Arg.Set_string ditto_flags,
        "Extra flags for each transformation command (transform only; default: \
         none)"
      );
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
            action = !action;
            statistic = !statistic;
            format = !format;
          }
    | None, _ -> Error.string_to_or_error "Please provide a path"
    | _, None -> Error.string_to_or_error "Please provide --output-folder"
  with
  | Arg.Bad msg -> Error.string_to_or_error msg
  | Arg.Help msg ->
      print_string msg;
      exit 0

let output_ditto_ninja_of_coqproject (opts : resolved_options) :
    (unit, Error.t) result =
  let ( let* ) = Result.bind in

  let* ninja_file = coqproject_to_ninja_file opts in
  Format.printf "%a\n%!" Ninja.pp ninja_file;
  Ok ()

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
