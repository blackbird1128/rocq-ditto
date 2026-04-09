[%%import "rocq_version_optcomp.mlh"]
[%%if rocq_version < (9, 1, 0)]

type ('a, 'b, 'c, 'occvar) t =
  [%import: ('a, 'b, 'c, 'occvar) Genredexpr.may_eval]

let make (x : ('a, 'b, 'c, 'occvar) Genredexpr.may_eval) = x

[%%else]

type ('a, 'b, 'c, 'occvar) t =
  [%import: ('a, 'b, 'c, 'occvar) Ltac_plugin.Tacexpr.may_eval]

let make (x : ('a, 'b, 'c, 'occvar) Ltac_plugin.Tacexpr.may_eval) = x

[%%endif]
