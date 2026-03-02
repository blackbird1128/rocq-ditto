val constrexpr_to_string : Constrexpr.constr_expr -> string
val get_cref_qualid : Constrexpr.constr_expr -> Libnames.qualid option

val get_fun_name_in_constrexpr :
  Constrexpr.constr_expr -> Libnames.qualid option

val get_fun_names_in_constrexpr : Constrexpr.constr_expr -> Libnames.qualid list
val get_func_args : Constrexpr.constr_expr -> Constrexpr.constr_expr list
val is_constrexpr_c_app_named : Constrexpr.constr_expr -> string -> bool
