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

let map_assert_constr_expr
    (f : Constrexpr.constr_expr -> Constrexpr.constr_expr)
    (tacexpr : Ltac_plugin.Tacexpr.raw_tactic_expr) :
    Ltac_plugin.Tacexpr.raw_tactic_expr =
  let open Ltac_plugin.Tacexpr in
  match tacexpr.v with
  | TacAtom (TacAssert (a, b, c, d, asrt)) ->
      TacAtom (TacAssert (a, b, c, d, Constrexpr_map.constr_expr_map f asrt))
      |> CAst.make
  | _ -> tacexpr

let map_bindings (f : Constrexpr.constr_expr -> Constrexpr.constr_expr)
    (bindings : Constrexpr.constr_expr Tactypes.bindings) :
    Constrexpr.constr_expr Tactypes.bindings =
  let map_constr = Constrexpr_map.constr_expr_map f in
  match bindings with
  | Tactypes.NoBindings -> Tactypes.NoBindings
  | Tactypes.ImplicitBindings args ->
      Tactypes.ImplicitBindings (List.map map_constr args)
  | Tactypes.ExplicitBindings args ->
      Tactypes.ExplicitBindings
        (List.map
           (fun (arg :
                  (Tactypes.quantified_hypothesis * Constrexpr.constr_expr)
                  CAst.t) ->
             let hyp, constr = arg.v in
             CAst.make ?loc:arg.loc (hyp, map_constr constr))
           args)

let map_bindings_list_arg (f : Constrexpr.constr_expr -> Constrexpr.constr_expr)
    (arg : Ltac_plugin.Tacexpr.r_dispatch Ltac_plugin.Tacexpr.gen_tactic_arg) :
    Ltac_plugin.Tacexpr.r_dispatch Ltac_plugin.Tacexpr.gen_tactic_arg =
  let open Ltac_plugin.Tacexpr in
  match arg with
  | TacGeneric (isquot, genarg) -> (
      match
        Raw_gen_args_converter.bindings_list_of_raw_generic_argument genarg
      with
      | Some bindings ->
          let mapped_bindings = List.map (map_bindings f) bindings in
          let atype = Genarg.Rawwit (Genarg.ListArg Tacarg.wit_bindings) in
          TacGeneric (isquot, Genarg.in_gen atype mapped_bindings)
      | None -> arg)
  | _ -> arg

let map_exists_constr_expr
    (f : Constrexpr.constr_expr -> Constrexpr.constr_expr)
    (tacexpr : Ltac_plugin.Tacexpr.raw_tactic_expr) :
    Ltac_plugin.Tacexpr.raw_tactic_expr =
  let open Ltac_plugin.Tacexpr in
  match tacexpr.v with
  | TacAlias (kername, args) ->
      let corelib_id = Names.Id.of_string "Corelib" in
      let init_id = Names.Id.of_string "Init" in
      let ltac_id = Names.Id.of_string "Ltac" in
      let ltac_dirpath = Names.DirPath.make [ ltac_id; init_id; corelib_id ] in
      let ltac_modpath = Names.ModPath.MPfile ltac_dirpath in

      let modpath, label = Names.KerName.repr kername in
      let label_string = Names.Label.to_string label in

      if
        Names.ModPath.equal modpath ltac_modpath
        && String.starts_with ~prefix:"exists" label_string
      then
        TacAlias (kername, List.map (map_bindings_list_arg f) args) |> CAst.make
      else tacexpr
  | _ -> tacexpr
