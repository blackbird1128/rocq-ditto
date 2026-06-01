[%%import "rocq_version_optcomp.mlh"]
[%%if rocq_version < (9, 1, 0)]

type ('a, 'b, 'c, 'occvar) t =
  ('a, 'b, 'c, 'occvar) Genredexpr.may_eval

let make (x : ('a, 'b, 'c, 'occvar) Genredexpr.may_eval) = x

let map_term (f : 'a -> 'a) (x : ('a, 'b, 'c, 'occvar) t) :
    ('a, 'b, 'c, 'occvar) t =
  match x with
  | Genredexpr.ConstrTerm term -> Genredexpr.ConstrTerm (f term)
  | Genredexpr.ConstrEval (red_expr_gen, term) ->
      Genredexpr.ConstrEval (red_expr_gen, f term)
  | Genredexpr.ConstrContext (name, term) ->
      Genredexpr.ConstrContext (name, f term)
  | Genredexpr.ConstrTypeOf term -> Genredexpr.ConstrTypeOf (f term)

[%%else]

type ('a, 'b, 'c, 'occvar) t =
  ('a, 'b, 'c, 'occvar) Ltac_plugin.Tacexpr.may_eval

let make (x : ('a, 'b, 'c, 'occvar) Ltac_plugin.Tacexpr.may_eval) = x

let map_term (f : 'a -> 'a) (x : ('a, 'b, 'c, 'occvar) t) :
    ('a, 'b, 'c, 'occvar) t =
  match x with
  | Ltac_plugin.Tacexpr.ConstrTerm term ->
      Ltac_plugin.Tacexpr.ConstrTerm (f term)
  | Ltac_plugin.Tacexpr.ConstrEval (red_expr_gen, term) ->
      Ltac_plugin.Tacexpr.ConstrEval (red_expr_gen, f term)
  | Ltac_plugin.Tacexpr.ConstrContext (name, term) ->
      Ltac_plugin.Tacexpr.ConstrContext (name, f term)
  | Ltac_plugin.Tacexpr.ConstrTypeOf term ->
      Ltac_plugin.Tacexpr.ConstrTypeOf (f term)

[%%endif]
