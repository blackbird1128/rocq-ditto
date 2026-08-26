open Ditto

type cli_args = { normalize : bool; path : string }

let get_ninja_rule () =
  let flagname = Rocq_version.executable_name ^ "flags" in
  let rule =
    Ninja.make_rule ~name:Rocq_version.executable_name
      ~command:
        (Printf.sprintf "%s $%s $in" Rocq_version.compiler_command flagname)
      ()
  in
  Ninja.rule rule

let normalize_path ~(project_dir : string) (path : string) : string =
  let with_sep =
    if Filename.check_suffix project_dir Filename.dir_sep then project_dir
    else project_dir ^ Filename.dir_sep
  in
  (path |> fun x -> String_utils.remove_prefix x with_sep) |> fun x ->
  String_utils.remove_prefix x "/"

let coqproject_to_ninja_file ~(normalize : bool) (project : Project.t) :
    (Ninja.t, Error.t) result =
  let ( let* ) = Result.bind in
  let* depgraph = Compile.coqproject_to_dep_graph project in
  let* depfiles = Compile.coqproject_sorted_files project in
  let project_dir = Filename.dirname (Project.path project) in
  let maybe_normalize =
    if normalize then normalize_path ~project_dir else Fun.id
  in
  let flagname = Rocq_version.executable_name ^ "flags" in
  let* args = Project.to_args project |> Result.map (String.concat " ") in

  let flags_var = Ninja.variable flagname args in

  let rule = get_ninja_rule () in

  let depsgraph_seq = Dependency_graph.to_seq depgraph |> List.of_seq in

  let builds =
    List.map
      (fun (file, neighbors) ->
        let filepath = file |> maybe_normalize |> Ninja.Path.v in
        let output_filepath =
          Filename.remove_extension file ^ ".vo"
          |> maybe_normalize |> Ninja.Path.v
        in
        let neighbors_paths =
          List.map
            (fun file ->
              let file_vo = Filename.remove_extension file ^ ".vo" in
              file_vo |> maybe_normalize |> Ninja.Path.v)
            neighbors
        in
        Ninja.make_build ~inputs:[ filepath ] ~outputs:[ output_filepath ]
          ~implicit:neighbors_paths ~rule:Rocq_version.executable_name ())
      depsgraph_seq
    |> List.map Ninja.build |> Ninja.concat
  in
  let default_paths =
    List.map
      (fun file ->
        let file_vo = Filename.remove_extension file ^ ".vo" in
        file_vo |> maybe_normalize |> Ninja.Path.v)
      depfiles
  in
  let defaults = Ninja.default default_paths in

  Ok (Ninja.concat [ flags_var; rule; builds; defaults ])

let output_ninja_of_coqproject ~(normalize : bool) (project : Project.t) :
    (unit, Error.t) result =
  let ( let* ) = Result.bind in

  let* ninja_file = coqproject_to_ninja_file ~normalize project in
  Format.printf "%a\n%!" Ninja.pp ninja_file;
  Ok ()

let parse_args () : (cli_args, Error.t) result =
  let path = ref None in
  let normalize = ref false in
  let usage_msg =
    Printf.sprintf "Usage: %s [options] <path>" (Filename.basename Sys.argv.(0))
  in
  let specs =
    [
      ( "-normalize",
        Arg.Set normalize,
        " Rewrite emitted ninja file paths relative to the _CoqProject \
         directory" );
      ("--normalize", Arg.Set normalize, " Same as -normalize");
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
    | Some path -> Ok { normalize = !normalize; path }
    | None -> Error.string_to_or_error "Please provide a path"
  with
  | Arg.Bad msg -> Error.string_to_or_error msg
  | Arg.Help msg ->
      print_string msg;
      exit 0

let get_project_ninja () : (unit, Error.t) result =
  let ( let* ) = Result.bind in
  let* { normalize; path } = parse_args () in

  let* project = Project.resolve_project_path path in

  output_ninja_of_coqproject ~normalize project

let main =
  match get_project_ninja () with
  | Ok _ -> exit 0
  | Error err ->
      Printf.eprintf "%s\n%!" (Error.to_string_hum err);
      exit 1

let () = main
