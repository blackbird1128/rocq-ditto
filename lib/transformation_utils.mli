open Proof

val map_raw_tactic_expr_in_node :
  (Ltac_plugin.Tacexpr.raw_tactic_expr -> Ltac_plugin.Tacexpr.raw_tactic_expr) ->
  Syntax_node.t ->
  transformation_step option

val map_definition_body :
  (Constrexpr.constr_expr -> Constrexpr.constr_expr) ->
  Syntax_node.t ->
  transformation_step option

val map_tacdef_bodies_in_node :
  (Ltac_plugin.Tacexpr.raw_tactic_expr -> Ltac_plugin.Tacexpr.raw_tactic_expr) ->
  (Constrexpr.constr_expr -> Constrexpr.constr_expr) ->
  Syntax_node.t ->
  transformation_step option
