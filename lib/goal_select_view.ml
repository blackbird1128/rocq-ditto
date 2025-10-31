[%%import "rocq_version_optcomp.mlh"]
[%%if rocq_version < (9, 1, 0)]

type goal_range_selector =
  | NthSelector of int
  | RangeSelector of int * int
  | IdSelector of Names.Id.t

let pp_goal_selector (fmt : Format.formatter) (x : goal_range_selector) =
  match x with
  | NthSelector nth -> Format.fprintf fmt "NthSelector %d" nth
  | RangeSelector (start, end_) ->
      Format.fprintf fmt "RangeSelector (%d,%d)" start end_
  | IdSelector name ->
      let name_str = Names.Id.to_string name in
      Format.fprintf fmt "IdSelector (%s)" name_str

type t =
  | SelectAlreadyFocused
  | SelectList of goal_range_selector list
  | SelectAll

let make (x : Goal_select.t) : t =
  match x with
  | Goal_select.SelectAlreadyFocused -> SelectAlreadyFocused
  | Goal_select.SelectNth nth -> SelectList [ NthSelector nth ]
  | Goal_select.SelectList range_list ->
      let l = List.map (fun (a, b) -> RangeSelector (a, b)) range_list in
      SelectList l
  | Goal_select.SelectId id -> SelectList [ IdSelector id ]
  | Goal_select.SelectAll -> SelectAll

[%%else]

type goal_range_selector = [%import: Proofview.goal_range_selector]
[@@derive show]

type t = [%import: Goal_select.t]

let make (x : Goal_select.t) : t = x

[%%endif]
