type path_kind = Dir | File

let is_directory (path : string) : bool =
  try
    let stats = Unix.stat path in
    stats.Unix.st_kind = Unix.S_DIR
  with Unix.Unix_error _ -> String.ends_with ~suffix:Filename.dir_sep path

let get_pathkind (path : string) : path_kind =
  if is_directory path then Dir else File

type newDirState = AlreadyExists | Created

let make_dir (dir_name : string) : (newDirState, Error.t) result =
  let perm = 0o755 in
  if Sys.file_exists dir_name then Ok AlreadyExists
  else
    try
      Unix.mkdir dir_name perm;
      Ok Created
    with Unix.Unix_error (err, _, _) ->
      Error.string_to_or_error (Unix.error_message err)

let copy_file (src : string) (dst : string) : (unit, Error.t) result =
  let buffer_size = 8192 in
  let buffer = Bytes.create buffer_size in
  try
    let ic = open_in_bin src in
    let oc = open_out_bin dst in
    let rec loop () =
      match input ic buffer 0 buffer_size with
      | 0 -> ()
      | n ->
          output oc buffer 0 n;
          loop ()
    in
    loop ();
    close_in ic;
    close_out oc;
    Ok ()
  with
  | Sys_error msg -> Error.string_to_or_error msg
  | e -> Error.string_to_or_error (Printexc.to_string e)
