val rename_name : string -> string -> Names.Name.t -> Names.Name.t
val rename_id : string -> string -> Names.Id.t -> Names.Id.t
val rename_lident : string -> string -> Names.lident -> Names.lident
val rename_lname : string -> string -> Names.lname -> Names.lname

val rename_taccall_tacarg_in_tacexpr :
  string ->
  string ->
  Ltac_plugin.Tacexpr.raw_tactic_expr ->
  Ltac_plugin.Tacexpr.raw_tactic_expr
