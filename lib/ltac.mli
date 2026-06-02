open Ltac_plugin

val ltac_tactic_extend_name : Vernacexpr.extend_name
val ltac_definition_extend_name : Vernacexpr.extend_name

val get_raw_atomic_tactic_expr :
  Tacexpr.raw_tactic_expr -> Tacexpr.raw_atomic_tactic_expr option

val get_alias_kername : Tacexpr.raw_tactic_expr -> Names.KerName.t option
val string_of_raw_tactic : Tacexpr.raw_tactic_expr -> string

val get_tac_generic_genarg :
  Ltac_plugin.Tacexpr.r_dispatch Ltac_plugin.Tacexpr.gen_tactic_arg ->
  Genarg.rlevel Genarg.generic_argument option

val map_assert_constr_expr :
  (Constrexpr.constr_expr -> Constrexpr.constr_expr) ->
  Ltac_plugin.Tacexpr.raw_tactic_expr ->
  Ltac_plugin.Tacexpr.raw_tactic_expr

val map_exists_constr_expr :
  (Constrexpr.constr_expr -> Constrexpr.constr_expr) ->
  Ltac_plugin.Tacexpr.raw_tactic_expr ->
  Ltac_plugin.Tacexpr.raw_tactic_expr
