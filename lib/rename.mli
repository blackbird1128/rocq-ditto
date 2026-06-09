val rename_name : string -> string -> Names.Name.t -> Names.Name.t
val rename_id : string -> string -> Names.Id.t -> Names.Id.t
val rename_lident : string -> string -> Names.lident -> Names.lident
val rename_lname : string -> string -> Names.lname -> Names.lname
val rename_qualid : string -> string -> Libnames.qualid -> Libnames.qualid
val rename_rcst : string -> string -> Genredexpr.r_cst -> Genredexpr.r_cst

val rename_ident_decl :
  string -> string -> Constrexpr.ident_decl -> Constrexpr.ident_decl

val rename_in_local_binder_expr :
  string ->
  string ->
  Constrexpr.local_binder_expr ->
  Constrexpr.local_binder_expr

val rename_in_vernac_assumption :
  string -> string -> Vernacexpr.vernac_expr -> Vernacexpr.vernac_expr

val rename_definition_node : string -> string -> Syntax_node.t -> Syntax_node.t

val rename_in_vernac_induction :
  string -> string -> Vernacexpr.vernac_expr -> Vernacexpr.vernac_expr

val rename_in_tac_reduce :
  string ->
  string ->
  Ltac_plugin.Tacexpr.raw_tactic_expr ->
  Ltac_plugin.Tacexpr.raw_tactic_expr

val rename_in_tac_arg :
  string ->
  string ->
  Ltac_plugin.Tacexpr.raw_tactic_expr ->
  Ltac_plugin.Tacexpr.raw_tactic_expr

val rename_taccall_tacarg_in_tacexpr :
  string ->
  string ->
  Ltac_plugin.Tacexpr.raw_tactic_expr ->
  Ltac_plugin.Tacexpr.raw_tactic_expr
