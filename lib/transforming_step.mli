type attach_position = LineAfter | LineBefore | SameLine
[@@deriving show { with_path = false }]

type t =
  | Remove of Uuidm.t
  | Replace of Uuidm.t * Syntax_node.t
  | Add of Syntax_node.t
  | Attach of Syntax_node.t * attach_position * Uuidm.t

val pp_transformation_step : Format.formatter -> t -> unit
val transformation_step_to_string : t -> string
