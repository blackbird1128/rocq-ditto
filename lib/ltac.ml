open Ltac_plugin

let get_raw_atomic_tactic_expr (x : Tacexpr.raw_tactic_expr) :
    Tacexpr.raw_atomic_tactic_expr option =
  match x.v with TacAtom expr -> Some expr | _ -> None

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
