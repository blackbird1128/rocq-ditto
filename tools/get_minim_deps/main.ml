open Ditto
module StringSet = Set.Make (String)

let print_minim_deps (project_dir : string) (project_filename : string)
    (subset_path : string) : (unit, Error.t) result =
  let ( let* ) = Result.bind in
  let project_path = Filename.concat project_dir project_filename in

  let* project_files = Compile.coqproject_sorted_files project_path in
  let normalized_project_files =
    List.map
      (Filesystem.normalize_path ~containing_dir:project_dir)
      project_files
  in

  let project_files_set = StringSet.of_list normalized_project_files in

  let* subset_files = Filesystem.read_nonempty_lines subset_path in
  let subset_files_set = StringSet.of_list subset_files in

  match
    StringSet.diff subset_files_set project_files_set |> StringSet.to_list
  with
  | [] ->
      let* dep_graph = Compile.coqproject_to_dep_graph project_path in
      let dep_graph_seq = Hashtbl.to_seq dep_graph in
      let dep_graph_seq_normalized =
        Seq.map
          (fun (a, neighbors) ->
            let normalized_a =
              Filesystem.normalize_path ~containing_dir:project_dir a
            in
            let normalized_neighbors =
              List.map
                (Filesystem.normalize_path ~containing_dir:project_dir)
                neighbors
            in
            (normalized_a, normalized_neighbors))
          dep_graph_seq
      in
      let dep_graph_normalized = Hashtbl.of_seq dep_graph_seq_normalized in

      let subset_needed =
        subset_files
        @ List.concat_map
            (fun file ->
              Compile.get_file_dependencies file dep_graph_normalized)
            subset_files
        |> List_utils.dedup
      in
      List.iter (fun file -> Printf.printf "%s\n%!" file) subset_needed;
      Ok ()
  | diff ->
      Error.format_to_or_error
        "The subset provided contains files that aren't in the _CoqProject \
         provided: %a"
        (Format.pp_print_list
           ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
           Format.pp_print_string)
        diff

(** The subset of files need to be relative to the _CoqProject folder *)
let get_minim_deps () =
  if Array.length Sys.argv != 3 then
    Error.string_to_or_error "Usage: get-minim-deps path subset-file-path"
  else
    let project_path = Sys.argv.(1) in
    let subset_path = Sys.argv.(2) in
    if not (Sys.file_exists project_path) then
      Error.string_to_or_error
        "Please provide a path to an existing file or directory for the \
         _CoqProject or _RocqProject"
    else if not (Sys.file_exists subset_path) then
      Error.string_to_or_error
        "Please provide a path to an existing file for the subset"
    else if Filesystem.is_directory project_path then
      match Compile.find_coqproject_dir_and_file project_path with
      | None ->
          Error.string_to_or_error
            "No _CoqProject or _RocqProject found in the directory provided"
      | Some (dir, filename) -> print_minim_deps dir filename subset_path
    else if
      Filename.basename project_path <> "_CoqProject"
      && Filename.basename project_path <> "_RocqProject"
    then
      Error.string_to_or_error
        "Please provide a path to a directory or to a _CoqProject or \
         _RocqProject file"
    else
      let path_dir = Filename.dirname project_path in
      let path_name = Filename.basename project_path in
      print_minim_deps path_dir path_name subset_path

let main =
  match get_minim_deps () with
  | Ok _ -> exit 0
  | Error err ->
      Printf.eprintf "%s\n%!" (Error.to_string_hum err);
      exit 1

let () = main
