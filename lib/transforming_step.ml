type attach_position = LineAfter | LineBefore | SameLine
[@@deriving show { with_path = false }]

type t =
  | Remove of Uuidm.t
  | Replace of Uuidm.t * Syntax_node.t
  | Add of Syntax_node.t
  | Attach of Syntax_node.t * attach_position * Uuidm.t

let pp_transformation_step (fmt : Format.formatter) (step : t) : unit =
  match step with
  | Remove id -> Format.fprintf fmt "Remove(%s)." (Uuidm.to_string id)
  | Replace (id, new_node) ->
      Format.fprintf fmt "Replace(%s, %s)" (Uuidm.to_string id)
        (Syntax_node.repr new_node)
  | Add new_node ->
      Format.fprintf fmt "Add(%s) at %s"
        (Syntax_node.repr new_node)
        (Code_range.to_string new_node.range)
  | Attach (attached_node, attach_position, anchor_id) ->
      Format.fprintf fmt "Attach(%s, %s, %s)"
        (Syntax_node.repr attached_node)
        (show_attach_position attach_position)
        (Uuidm.to_string anchor_id)

let transformation_step_to_string (step : t) : string =
  Format.asprintf "%a" pp_transformation_step step
