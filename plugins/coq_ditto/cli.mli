open Ditto
open Plugin_configuration

type transformation_options = {
  input : string;
  output : string;
  transformation : transformation_kind;
  verbose : bool;
  quiet : bool;
  save_vo : bool;
  reverse_order : bool;
  summary : bool;
  dependencies_action : dependencies_action;
  jobs : int option;
}

type transformation_settings = {
  transformation : transformation_kind;
  verbosity : verbosity;
  save_vo : bool;
  reverse_order : bool;
  summary : bool;
}

type document_options = {
  settings : transformation_settings;
  source : string;
  source_directory : string;
  destination : string;
  dependencies_action : dependencies_action;
}

type project_options = {
  settings : transformation_settings;
  source_directory : string;
  project : Project.t;
  destination : string;
  jobs : int;
}

type statistic_options = {
  input : string;
  statistic : statistic_kind;
  format : output_format;
}

type operation =
  | TransformDocument of document_options
  | TransformProject of project_options

(** Resolve transformation arguments into a document or project operation.
    Checks option compatibility and discovers the source project context. *)
val resolve : transformation_options -> (operation, Error.t) result

val transformation_help_fun :
  Plugin_configuration.transformation_kind ->
  Plugin_configuration.transformation_kind * string

val transformations_help :
  (Plugin_configuration.transformation_kind * string) list

val pp_level_lowercase : Format.formatter -> Logs.level -> unit
val pp_header_no_app : Format.formatter -> Logs.level * 'a -> unit
