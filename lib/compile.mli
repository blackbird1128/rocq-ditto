open Fleche

val find_coqproject_dir : string -> string option
val find_coqproject_file : string -> string option
val find_coqproject_dir_and_file : string -> (string * string) option
val coqproject_sorted_files : string -> (string list, Error.t) result

val resolve_project_path : string -> (string * string, Error.t) result
(** [resolve_project_path path] checks that the provided path is either a path
    to a directory containing a project file (_CoqProject or _RocqProject) or a
    path to a project file. If one if these condition is true, it returns the
    project directory of that path and the name of the project file, otherwise
    it returns an error *)

val coqproject_to_dep_graph :
  string -> ((string, string list) Hashtbl.t, Error.t) result

val coqproject_to_project_args : string -> (string list, Error.t) result
val depgraph_to_dot_format : (string, string list) Hashtbl.t -> string

val build_outdegrees : ('a, 'a list) Hashtbl.t -> ('a, int) Hashtbl.t
(** [build_outdegrees graph] compute the out-degree of each node in the graph,
    that is the number of outgoing edges starting at that node. In a dependency
    graph, that corresponds to the number of prerequisites of a file*)

val build_dependents : ('a, 'a list) Hashtbl.t -> ('a, 'a list) Hashtbl.t
(** [build_dependents graph] compute the direct dependents of each node of the
    graph, that is for each node, the list of nodes that can reach that node
    directly. In a dependency graph, that corresponds to each file that have the
    target node as a prerequisite *)

val get_file_dependencies :
  string -> (string, string list) Hashtbl.t -> string list
(** [get_file_dependencies file dependency_graph] compute the list of
    dependencies a file has in the dependency graph, recursively *)

val compile_file :
  Io.CallBack.t -> Doc.Env.t -> string -> (Doc.t, Error.t list) result
