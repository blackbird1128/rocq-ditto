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

val tacexpr_fold :
  ('acc -> Tacexpr.raw_tactic_expr -> 'acc) ->
  'acc ->
  Tacexpr.raw_tactic_expr ->
  'acc

val is_idtac : Tacexpr.raw_tactic_expr -> bool
val simplify : Tacexpr.raw_tactic_expr -> Tacexpr.raw_tactic_expr
val is_transparent_for_schedule : Tacexpr.raw_tactic_expr -> bool

val prefix_before :
  eq:(Tacexpr.raw_tactic_expr -> Tacexpr.raw_tactic_expr -> bool) ->
  target:Tacexpr.raw_tactic_expr ->
  Tacexpr.raw_tactic_expr ->
  Tacexpr.raw_tactic_expr option

val prefix_including :
  eq:(Tacexpr.raw_tactic_expr -> Tacexpr.raw_tactic_expr -> bool) ->
  target:Tacexpr.raw_tactic_expr ->
  Tacexpr.raw_tactic_expr ->
  Tacexpr.raw_tactic_expr option
