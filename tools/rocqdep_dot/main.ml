open Ditto

type cli_args = { path : string }

let output_dot_of_coqproject (project : Project.t) : (unit, Error.t) result =
  let ( let* ) = Result.bind in

  let* depgraph : Dependency_graph.t =
    Compile.coqproject_to_dep_graph project
  in
  let dep_seq = Dependency_graph.to_seq depgraph in
  let stripped_seq =
    Seq.map
      (fun (file, neighbors) ->
        let file_stripped =
          String_utils.remove_prefix file (Project.directory project)
        in
        let neighbors_stripped =
          List.map
            (fun x -> String_utils.remove_prefix x (Project.directory project))
            neighbors
        in
        (file_stripped, neighbors_stripped))
      dep_seq
  in
  let depgraph_stripped = Dependency_graph.of_seq stripped_seq in

  let dot_repr = Dependency_graph.to_dot_format depgraph_stripped in

  Printf.printf "%s%!" dot_repr;
  Ok ()

let parse_args () : (cli_args, Error.t) result =
  let path = ref None in
  let usage_msg =
    Printf.sprintf "Usage: %s <path>" (Filename.basename Sys.argv.(0))
  in

  let set_path arg =
    match !path with
    | None -> path := Some arg
    | Some _ -> raise (Arg.Bad "Please provide exactly one path")
  in

  try
    Arg.parse [] set_path usage_msg;
    match !path with
    | Some path -> Ok { path }
    | None -> Error.string_to_or_error "Please provide a path"
  with
  | Arg.Bad msg -> Error.string_to_or_error msg
  | Arg.Help msg ->
      print_string msg;
      exit 0

let get_project_dot () =
  let ( let* ) = Result.bind in

  let* { path } = parse_args () in

  let* project = Project.resolve_project_path path in
  output_dot_of_coqproject project

let main =
  match get_project_dot () with
  | Ok _ -> exit 0
  | Error err ->
      Printf.eprintf "%s\n%!" (Error.to_string_hum err);
      exit 1

let () = main
