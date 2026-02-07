open Ltac_plugin

val tacexpr_map_with_constr :
  (Tacexpr.raw_tactic_expr -> Tacexpr.raw_tactic_expr) ->
  (Constrexpr.constr_expr -> Constrexpr.constr_expr) ->
  Tacexpr.raw_tactic_expr ->
  Tacexpr.raw_tactic_expr

val tacexpr_map :
  (Tacexpr.raw_tactic_expr -> Tacexpr.raw_tactic_expr) ->
  Tacexpr.raw_tactic_expr ->
  Tacexpr.raw_tactic_expr
