open Ltac_plugin

val get_raw_atomic_tactic_expr :
  Tacexpr.raw_tactic_expr -> Tacexpr.raw_atomic_tactic_expr option
