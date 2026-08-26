type t

val path : t -> string
val directory : t -> string
val filename : t -> string
val find_project : string -> t option

val resolve_project_path : string -> (t, Error.t) result
(** [resolve_project_path path] checks that the provided path is either a path
    to a directory containing a project file (_CoqProject or _RocqProject) or a
    path to a project file. If one if these condition is true, it returns the
    project directory of that path and the name of the project file, otherwise
    it returns an error *)

val read_project_file : t -> (unit CoqProject_file.project, Error.t) result
val to_args : t -> (string list, Error.t) result
