open Fleche

type dependency_rule = { filename : string; dependencies : string list }
[@@deriving show { with_path = false }]

val coqproject_sorted_files : Project.t -> (string list, Error.t) result
val parse_depf_line : string -> (dependency_rule, Error.t) result

val parse_depf_output :
  string -> ((string, string list) Hashtbl.t, Error.t) result

val coqproject_to_dep_graph :
  Project.t -> ((string, string list) Hashtbl.t, Error.t) result

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

val parse_file :
  Io.CallBack.t -> Doc.Env.t -> string -> (Doc.t, Error.t list) result
