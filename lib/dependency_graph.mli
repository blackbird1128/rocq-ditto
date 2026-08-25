type t

val of_parents_table : (string, string list) Hashtbl.t -> t
val of_seq : (string * string list) Seq.t -> t
val to_seq : t -> (string * string list) Seq.t

val get_file_dependencies : string -> t -> (string list, Error.t) result
(** [get_file_dependencies file dependency_graph] compute the list of
    dependencies a file has in the dependency graph, recursively *)

val build_outdegrees : t -> (string, int) Hashtbl.t
(** [build_outdegrees graph] compute the out-degree of each node in the graph,
    that is the number of outgoing edges starting at that node. In a dependency
    graph, that corresponds to the number of prerequisites of a file*)

val build_dependents : t -> (string, string list) Hashtbl.t
(** [build_dependents graph] compute the direct dependents of each node of the
    graph, that is for each node, the list of nodes that can reach that node
    directly. In a dependency graph, that corresponds to each file that have the
    target node as a prerequisite *)

val to_dot_format : t -> string
