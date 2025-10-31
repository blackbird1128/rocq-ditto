type path_kind = Dir | File
type newDirState = AlreadyExists | Created

val is_directory : string -> bool
val get_pathkind : string -> path_kind
val copy_file : string -> string -> (unit, Error.t) result
val make_dir : string -> (newDirState, Error.t) result
