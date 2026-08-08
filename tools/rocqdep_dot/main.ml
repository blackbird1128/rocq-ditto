open Ditto

let output_dot_of_coqproject (project_dir : string) (project_filename : string)
    : (unit, Error.t) result =
  let ( let* ) = Result.bind in

  let project_path = Filename.concat project_dir project_filename in

  let* depgraph : (string, string list) Hashtbl.t =
    Compile.coqproject_to_dep_graph project_path
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

  Printf.printf "%s!" dot_repr;
  Ok ()

let get_project_dot () =
  let ( let* ) = Result.bind in
  if Array.length Sys.argv != 2 then
    Error.string_to_or_error "Usage: rocqdep-dot path"
  else
    let path = Sys.argv.(1) in

    let* project_dir, project_filename = Compile.resolve_project_path path in
    output_dot_of_coqproject project_dir project_filename

let main =
  match get_project_dot () with
  | Ok _ -> exit 0
  | Error err ->
      Printf.eprintf "%s\n%!" (Error.to_string_hum err);
      exit 1

let () = main
