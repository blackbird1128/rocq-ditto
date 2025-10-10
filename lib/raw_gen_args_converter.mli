open Sexplib.Sexp
open Ltac_plugin
open Serlib.Ser_extend

val raw_tactic_expr_of_raw_generic_argument :
  Genarg.raw_generic_argument -> Tacexpr.raw_tactic_expr option

val tacdef_body_of_raw_generic_argument :
  Genarg.raw_generic_argument -> Tacexpr.tacdef_body list option

val constr_expr_of_raw_generic_argument :
  Genarg.raw_generic_argument -> Constrexpr.constr_expr option

val intro_pattern_list_of_raw_generic_argument :
  Genarg.raw_generic_argument -> Tacexpr.intro_pattern list option

val intro_pattern_of_raw_generic_argument :
  Genarg.raw_generic_argument -> Tacexpr.intro_pattern option

val destruction_arg_of_raw_generic_argument :
  Genarg.raw_generic_argument ->
  (Constrexpr.constr_expr * 'a Tactypes.bindings)
  Serlib.Ser_tactics.destruction_arg
  option

val clause_expr_of_raw_generic_argument :
  Genarg.raw_generic_argument -> Tacexpr.t_nam CAst.t Locus.clause_expr option

val bindings_list_of_raw_generic_argument :
  Genarg.raw_generic_argument ->
  Constrexpr.constr_expr Tactypes.bindings list option

val id_of_raw_generic_argument :
  Genarg.raw_generic_argument -> Tacexpr.t_nam option

val hyp_list_of_raw_generic_argument :
  Genarg.raw_generic_argument -> Tacexpr.t_nam CAst.t list option

val hyp_of_raw_generic_argument :
  Genarg.raw_generic_argument -> Tacexpr.t_nam CAst.t option

val nat_or_var_of_raw_generic_argument :
  Genarg.raw_generic_argument -> int Locus.or_var list option

val auto_using_of_raw_generic_argument :
  Genarg.raw_generic_argument -> Constrexpr.constr_expr list option

val ltac_use_default_of_raw_generic_argument :
  Genarg.raw_generic_argument -> bool option

val ltac_of_raw_generic_argument :
  Genarg.raw_generic_argument -> Tacexpr.raw_tactic_expr option

val hintbases_of_raw_generic_argument :
  Genarg.raw_generic_argument -> string list option

val string_of_raw_generic_argument :
  Genarg.raw_generic_argument -> string option

val ref_of_raw_generic_argument :
  Genarg.raw_generic_argument -> Libnames.qualid option

val ref_list_of_raw_generic_argument :
  Genarg.raw_generic_argument -> Libnames.qualid list option

val opt_string_of_raw_generic_argument :
  Genarg.raw_generic_argument -> string option option

val by_arg_tac_of_raw_generic_argument :
  Genarg.raw_generic_argument -> Tacexpr.raw_tactic_expr list option

val clause_dft_concl_of_raw_generic_argument :
  Genarg.raw_generic_argument -> Tacexpr.t_nam CAst.t Locus.clause_expr option

val constr_with_bindings_of_raw_generic_argument :
  Genarg.raw_generic_argument ->
  Constrexpr.constr_expr Serlib.Ser_tactypes.with_bindings option

val rename_idents_of_raw_generic_argument :
  Genarg.raw_generic_argument -> (Tacexpr.t_nam * Tacexpr.t_nam) list option

val ltac_production_item_of_raw_generic_argument :
  Genarg.raw_generic_argument ->
  unit Pptactic.grammar_tactic_prod_item_expr list option

val ltac_tactic_level_of_raw_generic_argument :
  Genarg.raw_generic_argument -> int option option

val test_lpar_id_colon_of_raw_generic_argument :
  Genarg.raw_generic_argument -> unit option

val lconstr_of_raw_generic_argument :
  Genarg.raw_generic_argument -> Constrexpr.constr_expr option

val ltac_selector_of_raw_generic_argument :
  Genarg.raw_generic_argument -> Goal_select.t option option

type ltac_elements = {
  selector : Goal_select.t option;
  raw_tactic_expr : Ltac_plugin.Tacexpr.raw_tactic_expr;
  use_default : bool; (* TODO parse last args *)
}

val raw_arguments_to_ltac_elements :
  Genarg.raw_generic_argument list -> ltac_elements option

val raw_arguments_to_raw_tactic_expr :
  Genarg.raw_generic_argument list -> Ltac_plugin.Tacexpr.raw_tactic_expr option
