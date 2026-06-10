open Proof

val map_raw_tactic_expr_in_node :
  (Ltac_plugin.Tacexpr.raw_tactic_expr -> Ltac_plugin.Tacexpr.raw_tactic_expr) ->
  Syntax_node.t ->
  transformation_step option

val map_definition_body :
  (Constrexpr.constr_expr -> Constrexpr.constr_expr) ->
  Syntax_node.t ->
  transformation_step option

val map_definition_body_in_state :
  (Constrexpr.constr_expr -> Constrexpr.constr_expr) ->
  token:Coq.Limits.Token.t ->
  st:Coq.State.t ->
  Syntax_node.t ->
  (transformation_step option, Error.t) result

val map_tacdef_bodies_in_node :
  (Ltac_plugin.Tacexpr.raw_tactic_expr -> Ltac_plugin.Tacexpr.raw_tactic_expr) ->
  (Constrexpr.constr_expr -> Constrexpr.constr_expr) ->
  Syntax_node.t ->
  transformation_step option

val map_syntax_node :
  (Syntax_node.t -> Syntax_node.t) ->
  Syntax_node.t ->
  transformation_step option

val map_vernacexpr_in_node :
  (Vernacexpr.vernac_expr -> Vernacexpr.vernac_expr) ->
  Syntax_node.t ->
  transformation_step option

val map_vernacexpr_in_node_in_state :
  (Vernacexpr.vernac_expr -> Vernacexpr.vernac_expr) ->
  token:Coq.Limits.Token.t ->
  st:Coq.State.t ->
  Syntax_node.t ->
  (transformation_step option, Error.t) result
