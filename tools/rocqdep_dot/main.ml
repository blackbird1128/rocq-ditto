open Ditto
open Arg

let usage_msg = "rocqdep-dot <coqprojectpath>"

let output_dot_of_coqproject (project_dir : string) (project_filename : string)
    : (unit, Error.t) result =
  let ( let* ) = Result.bind in

  let project_path = Filename.concat project_dir project_filename in
  let* dep_files = Compile.coqproject_sorted_files project_path in

  let* depgraph : (string, string list) Hashtbl.t =
    Compile.coqproject_to_dep_graph project_path
  in
  let _pad_depgraph =
    List.iter
      (fun x -> if not (Hashtbl.mem depgraph x) then Hashtbl.add depgraph x [])
      dep_files
  in
  let dep_seq = Hashtbl.to_seq depgraph in
  let stripped_seq =
    Seq.map
      (fun (file, neighbors) ->
        let file_stripped = String_utils.remove_prefix file project_dir in
        let neighbors_stripped =
          List.map (fun x -> String_utils.remove_prefix x project_dir) neighbors
        in
        (file_stripped, neighbors_stripped))
      dep_seq
  in
  let depgraph_stripped = Hashtbl.of_seq stripped_seq in

  let dot_repr = Compile.depgraph_to_dot_format depgraph_stripped in

  Printf.printf "%s" dot_repr;
  Ok ()

let get_project_dot () =
  if Array.length Sys.argv != 2 then
    Error.string_to_or_error "Usage: rocqdep-dot file"
  else
    let path = Sys.argv.(1) in
    if not (Sys.file_exists path) then
      Error.string_to_or_error
        "Please provide a path to an existing file or directory"
    else if Filesystem.is_directory path then
      match Compile.find_coqproject_dir_and_file path with
      | None ->
          Error.string_to_or_error
            "No _CoqProject or _RocqProject found in the directory provided"
      | Some (dir, filename) -> output_dot_of_coqproject dir filename
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
      output_dot_of_coqproject path_dir path_name

let main =
  match get_project_dot () with
  | Ok _ -> exit 0
  | Error err ->
      Printf.eprintf "%s\n%!" (Error.to_string_hum err);
      exit 1

let () = main
