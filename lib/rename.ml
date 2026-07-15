[%%import "rocq_version_optcomp.mlh"]

(** renaming an identifier is a common enough operation to justify a separated
    module *)
(* TODO: review architecture *)

let rename_name (old_name : string) (new_name : string) (name : Names.Name.t) :
    Names.Name.t =
  let old_name_cast : Names.Name.t = Name (Names.Id.of_string old_name) in
  if Names.Name.equal old_name_cast name then Name (Names.Id.of_string new_name)
  else name

let rename_id (old_name : string) (new_name : string) (x : Names.Id.t) :
    Names.Id.t =
  let old_name_id = Names.Id.of_string old_name in
  if Names.Id.equal x old_name_id then Names.Id.of_string new_name else x

let rename_lident (old_name : string) (new_name : string) (x : Names.lident) :
    Names.lident =
  CAst.map (rename_id old_name new_name) x

let rename_lname (old_name : string) (new_name : string) (x : Names.lname) :
    Names.lname =
  CAst.map (rename_name old_name new_name) x

let rename_qualid (old_name : string) (new_name : string) (x : Libnames.qualid)
    : Libnames.qualid =
  let dirpath, id = Libnames.repr_qualid x in
  let mapped_id = rename_id old_name new_name id in
  Libnames.make_qualid dirpath mapped_id

let rename_rcst (old_name : string) (new_name : string) (x : Genredexpr.r_cst) :
    Genredexpr.r_cst =
  let old_name_qualid = Libnames.qualid_of_string old_name in
  let new_name_qualid = Libnames.qualid_of_string new_name in
  match x.v with
  | Constrexpr.AN qualid when Libnames.qualid_eq old_name_qualid qualid ->
      Constrexpr.AN new_name_qualid |> CAst.make
  | Constrexpr.ByNotation _ -> x
  | _ -> x

let rename_ident_decl (old_name : string) (new_name : string)
    (x : Constrexpr.ident_decl) : Constrexpr.ident_decl =
  (fun (lname, univ_decl_opt) ->
    (rename_lident old_name new_name lname, univ_decl_opt))
    x

let rename_in_local_binder_expr (old_name : string) (new_name : string)
    (x : Constrexpr.local_binder_expr) : Constrexpr.local_binder_expr =
  let rename_expr =
    Constrexpr_map.constr_expr_map
      (Constrexpr_utils.replace_fun_name_in_constrexpr old_name new_name)
  in
  match x with
  | Constrexpr.CLocalAssum (lnames, relevance, binder_kind, expr) ->
      Constrexpr.CLocalAssum
        ( List.map (rename_lname old_name new_name) lnames,
          relevance,
          binder_kind,
          rename_expr expr )
  | Constrexpr.CLocalDef (lname, relevance, expr, expr_opt) ->
      Constrexpr.CLocalDef
        ( rename_lname old_name new_name lname,
          relevance,
          rename_expr expr,
          Option.map rename_expr expr_opt )
  | Constrexpr.CLocalPattern _ -> x

let rename_in_inductive_params_expr (old_name : string) (new_name : string)
    (x : Vernacexpr.inductive_params_expr) : Vernacexpr.inductive_params_expr =
  let params, params_opt = x in
  ( List.map (rename_in_local_binder_expr old_name new_name) params,
    Option.map
      (List.map (rename_in_local_binder_expr old_name new_name))
      params_opt )

let rename_in_vernac_assumption (old_name : string) (new_name : string)
    (x : Vernacexpr.vernac_expr) : Vernacexpr.vernac_expr =
  match x with
  | VernacSynterp _ -> x
  | VernacSynPure expr -> (
      match expr with
      | VernacAssumption
          (discharge_assumption_kind, mods_inline, with_coercion_list) ->
          let mapped_with_coercion_list =
            List.map
              (fun (coercion, (ident_decl_list, constr_expr)) ->
                ( coercion,
                  ( List.map
                      (rename_ident_decl old_name new_name)
                      ident_decl_list,
                    constr_expr ) ))
              with_coercion_list
          in
          let mapped_synpure =
            Vernacexpr.VernacSynPure
              (Vernacexpr.VernacAssumption
                 ( discharge_assumption_kind,
                   mods_inline,
                   mapped_with_coercion_list ))
          in
          mapped_synpure
      | _ -> x)

let rename_definition_node (old_name : string) (new_name : string)
    (x : Syntax_node.t) : Syntax_node.t =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).v.expr with
      | VernacSynPure
          (Vernacexpr.VernacDefinition (kind, (name, name_univ), expr)) ->
          let name_mapped = rename_name old_name new_name name.v in
          if Names.Name.equal name.v name_mapped then x
          else
            let name_decl_mapped = (name_mapped |> CAst.make, name_univ) in
            let vernac_mapped =
              Vernacexpr.VernacSynPure
                (VernacDefinition (kind, name_decl_mapped, expr))
            in
            let vernac_control_mapped =
              Syntax_node.mk_vernac_control vernac_mapped
            in

            Syntax_node.of_coq_ast
              (Coq.Ast.of_coq vernac_control_mapped)
              x.range.start
      | _ -> x)
  | None -> x

let rename_in_glob_ref_flag (old_name : string) (new_name : string)
    (grf : Genredexpr.r_cst Genredexpr.glob_red_flag) :
    Genredexpr.r_cst Genredexpr.glob_red_flag =
  { grf with rConst = List.map (rename_rcst old_name new_name) grf.rConst }

let rec rename_in_gen_tactic_arg (old_name : string) (new_name : string)
    (x : Ltac_plugin.Tacexpr.r_dispatch Ltac_plugin.Tacexpr.gen_tactic_arg) :
    Ltac_plugin.Tacexpr.r_dispatch Ltac_plugin.Tacexpr.gen_tactic_arg =
  let open Ltac_plugin.Tacexpr in
  match x with
  | TacGeneric _ -> x
  | ConstrMayEval _ -> x
  | Reference reference -> Reference (rename_qualid old_name new_name reference)
  | TacCall call_args ->
      let qualid, args = call_args.v in
      let mapped_qualid = rename_qualid old_name new_name qualid in
      let mapped_args =
        List.map (rename_in_gen_tactic_arg old_name new_name) args
      in
      let mapped_call_args =
        CAst.make ?loc:call_args.loc (mapped_qualid, mapped_args)
      in
      TacCall mapped_call_args
  | TacFreshId _ -> x
  | Tacexp _ -> x
  | TacPretype cexpr ->
      let mapped_cexpr =
        Constrexpr_map.constr_expr_map
          (Constrexpr_utils.replace_fun_name_in_constrexpr old_name new_name)
          cexpr
      in
      TacPretype mapped_cexpr
  | TacNumgoals -> x

let rename_in_tac_arg (old_name : string) (new_name : string)
    (x : Ltac_plugin.Tacexpr.raw_tactic_expr) :
    Ltac_plugin.Tacexpr.raw_tactic_expr =
  let open Ltac_plugin.Tacexpr in
  match x.v with
  | TacArg args ->
      TacArg (rename_in_gen_tactic_arg old_name new_name args)
      |> CAst.make ?loc:x.loc
  | _ -> x

let rename_in_tac_reduce (old_name : string) (new_name : string)
    (x : Ltac_plugin.Tacexpr.raw_tactic_expr) :
    Ltac_plugin.Tacexpr.raw_tactic_expr =
  let open Ltac_plugin in
  match x.v with
  (* tacReduce will change in 9.3 :[ *)
  | TacAtom (TacReduce (user_red_expr, clause_expr)) -> (
      match user_red_expr with
      | Genredexpr.Simpl (_glob_red_flag, _) -> x
      | Genredexpr.Cbv glob_red_flag ->
          Tacexpr.TacAtom
            (TacReduce
               ( Genredexpr.Cbv
                   (rename_in_glob_ref_flag old_name new_name glob_red_flag),
                 clause_expr ))
          |> CAst.make
      | Genredexpr.Cbn glob_red_flag ->
          Tacexpr.TacAtom
            (TacReduce
               ( Genredexpr.Cbn
                   (rename_in_glob_ref_flag old_name new_name glob_red_flag),
                 clause_expr ))
          |> CAst.make
      | Genredexpr.Lazy glob_red_flag ->
          Tacexpr.TacAtom
            (TacReduce
               ( Genredexpr.Lazy
                   (rename_in_glob_ref_flag old_name new_name glob_red_flag),
                 clause_expr ))
          |> CAst.make
      | Genredexpr.Unfold occs ->
          let mapped_occs =
            List.map
              (fun (occs_gen, r_cst) ->
                (occs_gen, rename_rcst old_name new_name r_cst))
              occs
          in
          Tacexpr.TacAtom
            (TacReduce (Genredexpr.Unfold mapped_occs, clause_expr))
          |> CAst.make
      | Genredexpr.Fold constrexpr_list ->
          Tacexpr.TacAtom
            (TacReduce
               ( Genredexpr.Fold
                   (List.map
                      (Constrexpr_utils.replace_fun_name_in_constrexpr old_name
                         new_name)
                      constrexpr_list),
                 clause_expr ))
          |> CAst.make
      | Genredexpr.Pattern _ -> x
      | Genredexpr.ExtraRedExpr _ -> x
      | Genredexpr.CbvVm _ -> x
      | Genredexpr.CbvNative _ -> x
      | _ -> x)
  | _ -> x

(** If [tacexpr] is exactly a TacArg(TacCall ...), rename the called qualid. *)
let rename_taccall_tacarg_in_tacexpr (old_taccall_name : string)
    (new_taccall_name : string) (tacexpr : Ltac_plugin.Tacexpr.raw_tactic_expr)
    : Ltac_plugin.Tacexpr.raw_tactic_expr =
  let open Ltac_plugin.Tacexpr in
  match tacexpr.v with
  | TacArg (TacCall call_arg) ->
      let old_call_qualid, old_call_args = call_arg.v in
      let old_call_qualid_str = Libnames.string_of_qualid old_call_qualid in
      if old_call_qualid_str = old_taccall_name then
        let new_taccall_name_qualid =
          Libnames.qualid_of_string new_taccall_name
        in
        let new_taccall = CAst.make (new_taccall_name_qualid, old_call_args) in
        TacArg (TacCall new_taccall) |> CAst.make
      else tacexpr
  | _ -> tacexpr

[%%if rocq_version < (9, 1, 0)]

let interp_context_evars_env_bl ~program_mode ~impl_env env sigma lbe =
  let sigma, (impls, ((env_bl, _ctx), _imps)) =
    Constrintern.interp_context_evars ~program_mode ~impl_env env sigma lbe
  in

  (sigma, impls, env_bl)

[%%else]

let interp_context_evars_env_bl ~program_mode ~impl_env env sigma lbe =
  let sigma, (impls, ((env_bl, _ctx), _imps, _locs)) =
    Constrintern.interp_context_evars ~program_mode ~impl_env env sigma lbe
  in

  (sigma, impls, env_bl)

[%%endif]

let infer_type_expr (env : Environ.env) (sigma : Evd.evar_map)
    (impls_env : Constrintern.internalization_env)
    (lbe : Constrexpr.local_binder_expr list) (expr : Constrexpr.constr_expr) =
  let sigma, impls, env_bl =
    interp_context_evars_env_bl ~program_mode:false ~impl_env:impls_env env
      sigma lbe
  in
  let sigma, (body, _impsbody) =
    Constrintern.interp_constr_evars_impls ~program_mode:false env_bl sigma
      ~impls expr
  in
  let typ = Retyping.get_type_of env_bl sigma body in
  (sigma, Constrextern.extern_type env_bl sigma typ)

let type_expr (env : Environ.env) (sigma : Evd.evar_map)
    (impls_env : Constrintern.internalization_env)
    (lbe : Constrexpr.local_binder_expr list) (expr : Constrexpr.constr_expr)
    (expr_opt : Constrexpr.constr_expr option) =
  match expr_opt with
  | Some t -> (sigma, t)
  | None -> infer_type_expr env sigma impls_env lbe expr

let constr_expr_opt_eq (x : Constrexpr.constr_expr option)
    (y : Constrexpr.constr_expr option) : bool =
  match (x, y) with
  | None, None -> true
  | Some x, Some y -> Constrexpr_ops.constr_expr_eq x y
  | _ -> false

let local_binder_expr_eq (x : Constrexpr.local_binder_expr)
    (y : Constrexpr.local_binder_expr) : bool =
  match (x, y) with
  | ( CLocalAssum (lnames, relevance, binder_kind, expr),
      CLocalAssum (lnames', relevance', binder_kind', expr') ) ->
      lnames = lnames' && relevance = relevance' && binder_kind = binder_kind'
      && Constrexpr_ops.constr_expr_eq expr expr'
  | ( CLocalDef (lname, relevance, expr, expr_opt),
      CLocalDef (lname', relevance', expr', expr_opt') ) ->
      lname = lname' && relevance = relevance'
      && Constrexpr_ops.constr_expr_eq expr expr'
      && constr_expr_opt_eq expr_opt expr_opt'
  | CLocalPattern p, CLocalPattern p' -> p = p'
  | _, _ -> false

let local_binder_expr_list_eq = List.equal local_binder_expr_eq

let rename_in_local_decl_expr (old_name : string) (new_name : string)
    (x : Vernacexpr.local_decl_expr) : Vernacexpr.local_decl_expr =
  let rename_expr =
    Constrexpr_map.constr_expr_map
      (Constrexpr_utils.replace_fun_name_in_constrexpr old_name new_name)
  in
  let rename_binders =
    List.map (rename_in_local_binder_expr old_name new_name)
  in

  match x with
  | Vernacexpr.AssumExpr (lname, lbe, expr) ->
      let mapped_lname = rename_lname old_name new_name lname in
      let mapped_lbe = rename_binders lbe in
      let mapped_expr = rename_expr expr in
      if
        lname = mapped_lname
        && local_binder_expr_list_eq lbe mapped_lbe
        && Constrexpr_ops.constr_expr_eq expr mapped_expr
      then x
      else Vernacexpr.AssumExpr (mapped_lname, mapped_lbe, mapped_expr)
  | Vernacexpr.DefExpr (lname, lbe, expr, expr_opt) ->
      let mapped_lname = rename_lname old_name new_name lname in
      let mapped_lbe = rename_binders lbe in
      let mapped_expr = rename_expr expr in
      let mapped_expr_opt = Option.map rename_expr expr_opt in
      if
        lname = mapped_lname
        && local_binder_expr_list_eq lbe mapped_lbe
        && Constrexpr_ops.constr_expr_eq expr mapped_expr
        && constr_expr_opt_eq expr_opt mapped_expr_opt
      then x
      else
        let mapped_expr_opt =
          match (mapped_lbe, mapped_expr_opt) with
          | [], _ | _, Some _ -> mapped_expr_opt
          | _ :: _, None ->
              let env = Global.env () in
              let sigma = Evd.from_env env in
              let impls_env = Constrintern.empty_internalization_env in
              let _sigma, t =
                type_expr env sigma impls_env mapped_lbe mapped_expr
                  mapped_expr_opt
              in
              Some t
        in

        Vernacexpr.DefExpr
          (mapped_lname, mapped_lbe, mapped_expr, mapped_expr_opt)

(* Constrexpr.cumul_ident_decl Vernacexpr.with_coercion *)
(* * Vernacexpr.inductive_params_expr *)
(* * Constrexpr.constr_expr option *)
(* * Vernacexpr.constructor_list_or_record_decl_expr *)

(* renaming in inductive expr is a bit ambiguous, there is multiple construct handled:
   - Inductive
   - Mutual inductive
   - Record
   - Class
   - Variant
   - Structure

   cumul_ident_with_coerc contains the name of the inductive
   
 *)

let rename_in_record_field (old_name : string) (new_name : string)
    (x : Vernacexpr.local_decl_expr * Vernacexpr.record_field_attr_unparsed) :
    Vernacexpr.local_decl_expr * Vernacexpr.record_field_attr_unparsed =
  let local_decl, record_field_attr = x in
  (rename_in_local_decl_expr old_name new_name local_decl, record_field_attr)

let rename_in_constructor_list_or_record_decl_expr (old_name : string)
    (new_name : string) (x : Vernacexpr.constructor_list_or_record_decl_expr) :
    Vernacexpr.constructor_list_or_record_decl_expr =
  match x with
  | Constructors _ ->
      x
      (* for now we ignore constructors, might be interesting at some points tho *)
  | RecordDecl (name_opt, fields, ident_opt) ->
      (* The first ident is the name of the record *)
      (* the second ident is for record syntax using as ident. *)
      RecordDecl
        ( name_opt,
          List.map (rename_in_record_field old_name new_name) fields,
          ident_opt )

let rename_in_inductive_expr (old_name : string) (new_name : string)
    (x : Vernacexpr.inductive_expr) : Vernacexpr.inductive_expr =
  let ( cumul_ident_with_coerc,
        ind_params_expr,
        opt_expr,
        cons_list_or_record_decl ) =
    x
  in

  let rename_expr =
    Constrexpr_map.constr_expr_map
      (Constrexpr_utils.replace_fun_name_in_constrexpr old_name new_name)
  in
  ( cumul_ident_with_coerc,
    rename_in_inductive_params_expr old_name new_name ind_params_expr,
    Option.map rename_expr opt_expr,
    rename_in_constructor_list_or_record_decl_expr old_name new_name
      cons_list_or_record_decl )

let rename_in_vernac_induction (old_name : string) (new_name : string)
    (x : Vernacexpr.vernac_expr) : Vernacexpr.vernac_expr =
  match x with
  | VernacSynterp _ -> x
  | VernacSynPure expr -> (
      match expr with
      | VernacInductive (ind_kind, ind_list) ->
          Vernacexpr.VernacSynPure
            (Vernacexpr.VernacInductive
               ( ind_kind,
                 List.map
                   (fun (ind_expr, notation_decl_l) ->
                     ( rename_in_inductive_expr old_name new_name ind_expr,
                       notation_decl_l ))
                   ind_list ))
      | _ -> x)
