[%%import "rocq_version_optcomp.mlh"]
[%%if rocq_version < (9, 1, 0)]

type goal_range_selector =
  | NthSelector of int
  | RangeSelector of int * int
  | IdSelector of Names.Id.t

type t =
  | SelectAlreadyFocused
  | SelectList of goal_range_selector list
  | SelectAll

val make : Goal_select.t -> t

[%%else]

type goal_range_selector = [%import: Proofview.goal_range_selector]
[@@derive show]

type t = [%import: Goal_select.t]

val make : Goal_select.t -> t

[%%endif]

val pp_goal_range_selector : Format.formatter -> goal_range_selector -> unit
val goal_range_selector_to_string : goal_range_selector -> string
val pp : Format.formatter -> t -> unit
val to_string : t -> string

val apply_goal_selector_view :
  t ->
  'a Coq.Goals.Reified_goal.t list ->
  ('a Coq.Goals.Reified_goal.t list, Error.t) result
