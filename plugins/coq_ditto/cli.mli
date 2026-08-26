open Ditto

type transformation_kind =
  | RenameDefinition
  | ExplicitFreshVariables
  | TurnIntoOneliner
  | ReplaceAutoWithSteps
  | FlattenGoalSelectors
  | CompressIntro
  | ReplaceInductionWithDestruct
  | ExplicitIdentInIntro
  | ExplicitApply
  | AddProofNodeIfMissing
  | RemoveProofWith
  | IdProofTransformation
  | IdDocTransformation
  | ConstructiviseGeocoq
  | RocqToLean
[@@deriving show { with_path = false }, enum]

type statistic_kind = CountInduction
[@@deriving show { with_path = false }, enum]

type dependencies_action =
  | NoAction
  | CompileDependencies
  | TransformDependencies
[@@deriving show { with_path = false }, enum]

type output_format = Text | Json [@@deriving show { with_path = false }]

type progress = private { current_file_count : int; total_file_count : int }
[@@deriving show { with_path = false }]

type verbosity = Quiet | Normal | Verbose

type transformation_configuration = private {
  progress : progress option;
  verbosity : verbosity;
  transformation_steps : transformation_kind list;
  reverse_order : bool;
  output_filename : string;
  save_vo : bool;
}

type statistic_configuration = private {
  format : output_format;
  statistic_kind : statistic_kind;
}

type plugin_configuration = private
  | StatisticAction of statistic_configuration
  | TransformationAction of transformation_configuration

type env = private (string * string) list

val create_progress : int -> int -> (progress, Error.t) result
val camel_to_snake : string -> string
val transformation_kind_to_string : transformation_kind -> string
val statistic_kind_to_string : statistic_kind -> string
val dependencies_action_to_string : dependencies_action -> string
val output_format_to_string : output_format -> string
val all_transformation_kinds : transformation_kind list
val all_statistic_kinds : statistic_kind list
val all_dependencies_action : dependencies_action list
val transformations_list : string list
val statistics_list : string list

val transformation_help_fun :
  transformation_kind -> transformation_kind * string

val transformations_help : (transformation_kind * string) list
val suggest_spelling : string -> string list -> string option
val arg_to_output_format : string -> (output_format, Error.t) result
val arg_to_transformation_kind : string -> (transformation_kind, Error.t) result
val arg_to_statistic_kind : string -> (statistic_kind, Error.t) result
val arg_to_dependencies_action : string -> (dependencies_action, Error.t) result

val verbosity_of_flags :
  verbose:bool -> quiet:bool -> (verbosity, Error.t) result

val add_to_env_preserving : string array -> string * string -> string array
val extend_env : string array -> (string * string) list -> string array
val env_of_array : string array -> (env, Error.t) result
val get_env : env -> string -> (string, Error.t) result
val get_env_opt : env -> string -> string option
val int_of_string_err : string -> (int, Error.t) result
val get_env_as_bool_default : env -> string -> bool -> (bool, Error.t) result

val parse_transformation_steps :
  string -> (transformation_kind list, Error.t) result

val statistic_configuration_of_env :
  env -> (statistic_configuration, Error.t) result

val progress_of_env : env -> (progress option, Error.t) result

val transformation_configuration_of_env :
  env -> (transformation_configuration, Error.t) result

val plugin_configuration_of_env :
  string array -> (plugin_configuration, Error.t) result

val pp_level_lowercase : Format.formatter -> Logs.level -> unit
val pp_header_no_app : Format.formatter -> Logs.level * 'a -> unit
