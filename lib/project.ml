type t = { directory : string; filename : string; path : string }

let path (project : t) : string = project.path
let directory (project : t) : string = project.directory
let filename (project : t) : string = project.filename

let rec find_project (dir : string) : t option =
  let coqproject_filename = "_CoqProject" in
  let rocqproject_filename = "_RocqProject" in
  if Sys.file_exists (Filename.concat dir coqproject_filename) then
    Some
      {
        directory = dir;
        filename = coqproject_filename;
        path = Filename.concat dir coqproject_filename;
      }
  else if Sys.file_exists (Filename.concat dir rocqproject_filename) then
    Some
      {
        directory = dir;
        filename = rocqproject_filename;
        path = Filename.concat dir rocqproject_filename;
      }
  else if dir = "/" || dir = "." then None
  else find_project (Filename.dirname dir)

let resolve_project_path (path : string) : (t, Error.t) result =
  if not (Sys.file_exists path) then
    Error.string_to_or_error
      "Please provide a path to an existing file or directory"
  else if Filesystem.is_directory path then
    match find_project path with
    | None -> Error.string_to_or_error "No _CoqProject or _RocqProject found"
    | Some project -> Ok project
  else
    match Filename.basename path with
    | "_CoqProject" | "_RocqProject" ->
        Ok
          {
            directory = Filename.dirname path;
            filename = Filename.basename path;
            path;
          }
    | _ ->
        Error.string_to_or_error
          "Please provide a directory or a project file path"

let read_project_file (project : t) :
    (unit CoqProject_file.project, Error.t) result =
  let ( let* ) = Result.bind in
  let open CoqProject_file in
  let* proj =
    try Ok (read_project_file ~warning_fn:(fun _ -> ()) project.path)
    with Parsing_error err_msg | UnableToOpenProjectFile err_msg ->
      Error.string_to_or_error err_msg
  in
  Ok proj

let to_args (project : t) : (string list, Error.t) result =
  let ( let* ) = Result.bind in
  let* proj = read_project_file project in
  Ok (CoqProject_file.coqtop_args_from_project proj)
