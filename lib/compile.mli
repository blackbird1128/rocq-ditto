open Fleche

type dependency_rule = { filename : string; dependencies : string list }
[@@deriving show { with_path = false }]

val coqproject_sorted_files : Project.t -> (string list, Error.t) result
val parse_depf_line : string -> (dependency_rule, Error.t) result
val parse_depf_output : string -> (Dependency_graph.t, Error.t) result
val coqproject_to_dep_graph : Project.t -> (Dependency_graph.t, Error.t) result

val parse_file :
  Io.CallBack.t -> Doc.Env.t -> string -> (Doc.t, Error.t list) result
