open Ltac_plugin

let ltac_tactic_extend_name : Vernacexpr.extend_name =
  {
    ext_plugin = Rocq_version.ltac_ext_plugin_name;
    ext_entry = "VernacSolve";
    ext_index = 0;
  }

let ltac_definition_extend_name : Vernacexpr.extend_name =
  {
    ext_plugin = Rocq_version.ltac_ext_plugin_name;
    ext_entry = "VernacDeclareTacticDefinition";
    ext_index = 0;
  }

let get_raw_atomic_tactic_expr (t : Tacexpr.raw_tactic_expr) :
    Tacexpr.raw_atomic_tactic_expr option =
  match t.v with TacAtom expr -> Some expr | _ -> None

let get_alias_kername (t : Tacexpr.raw_tactic_expr) : Names.KerName.t option =
  match t.v with
  | Ltac_plugin.Tacexpr.TacAlias (kn, _args) -> Some kn
  | _ -> None

let string_of_raw_tactic (tac : Ltac_plugin.Tacexpr.raw_tactic_expr) : string =
  let env = Global.env () in
  let evd = Evd.from_env env in
  Ltac_plugin.Pptactic.pr_raw_tactic env evd tac |> Pp.string_of_ppcmds

let get_tac_generic_genarg
    (x : Ltac_plugin.Tacexpr.r_dispatch Ltac_plugin.Tacexpr.gen_tactic_arg) :
    Genarg.rlevel Genarg.generic_argument option =
  match x with
  | Ltac_plugin.Tacexpr.TacGeneric (_, genarg) -> Some genarg
  | _ -> None
