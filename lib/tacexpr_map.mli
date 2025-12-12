open Ltac_plugin

val tacexpr_map :
  (Tacexpr.raw_tactic_expr -> Tacexpr.raw_tactic_expr) ->
  Tacexpr.raw_tactic_expr ->
  Tacexpr.raw_tactic_expr * bool
