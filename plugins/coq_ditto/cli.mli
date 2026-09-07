val transformation_help_fun :
  Plugin_configuration.transformation_kind ->
  Plugin_configuration.transformation_kind * string

val transformations_help :
  (Plugin_configuration.transformation_kind * string) list

val pp_level_lowercase : Format.formatter -> Logs.level -> unit
val pp_header_no_app : Format.formatter -> Logs.level * 'a -> unit
