open Ltac_plugin

val ltac_tactic_extend_name : Vernacexpr.extend_name
val ltac_definition_extend_name : Vernacexpr.extend_name

val get_raw_atomic_tactic_expr :
  Tacexpr.raw_tactic_expr -> Tacexpr.raw_atomic_tactic_expr option
