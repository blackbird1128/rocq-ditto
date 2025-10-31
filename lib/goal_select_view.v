[%%import "rocq_version_optcomp.mlh"]
[%%if rocq_version < (9,1,0)]

type t =
| SelectAlreadyFocused
| SelectList of Proofview.goal_range_selector list
| SelectAll

[%%else]

type t = [%import: Goal_select.t]

[%%endif]
