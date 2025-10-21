open Ltac_plugin

val get_raw_atomic_tactic_expr :
  Tacexpr.raw_tactic_expr -> Tacexpr.raw_atomic_tactic_expr option

open Ltac_plugin.Tacexpr

type mapper = {
  map_expr : mapper -> raw_tactic_expr -> raw_tactic_expr;
  map_atom :
    mapper ->
    r_dispatch gen_atomic_tactic_expr ->
    r_dispatch gen_atomic_tactic_expr;
  map_arg : mapper -> r_dispatch gen_tactic_arg -> r_dispatch gen_tactic_arg;
}

val default_mapper : mapper
val replace_fail_with_id : mapper
