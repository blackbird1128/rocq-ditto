let with_opaque_access (full_state : Vernactypes.full_state)
    (f : Global.indirect_accessor -> 'a) : 'a =
  let open Vernactypes in
  let computation =
    typed_vernac_gen { ignore_state with opaque_access = OpaqueAccess.Access }
      (fun state ->
        let result = f state.opaque_access in
        (no_state, result))
  in
  let _, result = run computation full_state in
  result

let full_state_of_state (st : Coq.State.t) : Vernactypes.full_state =
  let (rocq_state : Vernacstate.t) = Coq.State.to_coq st in
  {
    prog = rocq_state.interp.program;
    proof = rocq_state.interp.lemmas;
    opaque_access = ();
  }

let constant_of_global_ref (gref : Names.GlobRef.t) : Names.Constant.t option =
  match gref with Names.GlobRef.ConstRef constant -> Some constant | _ -> None

let get ~(token : Coq.Limits.Token.t) (state : Coq.State.t)
    (constant : Names.Constant.t) : (Constr.t option, Error.t) result =
  Coq.State.in_state ~token ~st:state
    ~f:(fun constant ->
      let full_state = full_state_of_state state in
      let body_and_univ_opt =
        with_opaque_access full_state (fun opaque_access ->
            Global.body_of_constant opaque_access constant)
      in
      match body_and_univ_opt with
      | Some (term, _, _) -> Some term
      | None -> None)
    constant
  |> Error.protect_to_result

type name_ref =
  | Var of Names.Id.t
  | Const of Names.Constant.t
  | Inductive of Names.inductive

let pp_name_ref (fmt : Format.formatter) (name_ref : name_ref) : unit =
  match name_ref with
  | Var var_name -> Format.fprintf fmt "Var(%s)" (Names.Id.to_string var_name)
  | Const const_name ->
      Format.fprintf fmt "Const(%s)" (Names.Constant.debug_to_string const_name)
  | Inductive (ind_name, _ind_idx) ->
      Format.fprintf fmt "Inductive(%s)" (Names.MutInd.debug_to_string ind_name)

let name_ref_to_string (name_ref : name_ref) : string =
  Format.asprintf "%a" pp_name_ref name_ref

let name_ref_to_json (name_ref : name_ref) : Yojson.Safe.t =
  match name_ref with
  | Var var_name -> `Assoc [ ("var", `String (Names.Id.to_string var_name)) ]
  | Const const_name ->
      `Assoc [ ("const", `String (Names.Constant.debug_to_string const_name)) ]
  | Inductive (ind_name, _ind_idx) ->
      `Assoc [ ("inductive", `String (Names.MutInd.debug_to_string ind_name)) ]

let collect_names (term : Constr.t) : name_ref list =
  let rec aux_invert (acc : name_ref list) (invert : Constr.case_invert) =
    match invert with
    | Constr.NoInvert -> acc
    | Constr.CaseInvert { indices } -> Array.fold_left aux_constr acc indices
  and aux_constr (acc : name_ref list) (term : Constr.t) =
    match Constr.kind term with
    | Constr.Rel _ -> acc
    | Constr.Var name -> Var name :: acc
    | Constr.Meta _ -> acc
    | Constr.Evar (_, args) -> SList.Skip.fold aux_constr acc args
    | Constr.Sort _ -> acc
    | Constr.Cast (init_term, _, end_term) ->
        let acc_init = aux_constr acc init_term in
        aux_constr acc_init end_term
    | Constr.Prod (_, c1, c2) ->
        let acc_c1 = aux_constr acc c1 in
        aux_constr acc_c1 c2
    | Constr.Lambda (_, domain, body) ->
        let acc_domain = aux_constr acc domain in
        aux_constr acc_domain body
    | Constr.LetIn (_, c1, c2, c3) ->
        let acc_c1 = aux_constr acc c1 in
        let acc_c2 = aux_constr acc_c1 c2 in
        aux_constr acc_c2 c3
    | Constr.App (app_constr, app_args) ->
        let acc_app = aux_constr acc app_constr in
        Array.fold_left aux_constr acc_app app_args
    | Constr.Const (c, _) -> Const c :: acc
    | Constr.Ind (ind, _) -> Inductive ind :: acc
    | Constr.Construct (cons, _) ->
        let ind = Names.inductive_of_constructor cons in
        Inductive ind :: acc
    | Constr.Case
        ( info,
          _univ,
          params,
          ((_, pred_return_type), _),
          invert,
          scrutinee,
          branches ) ->
        let acc = Inductive info.ci_ind :: acc in
        let acc_params = Array.fold_left aux_constr acc params in
        let acc_pred_return_type = aux_constr acc_params pred_return_type in
        let acc_invert = aux_invert acc_pred_return_type invert in
        let acc_scrutinee = aux_constr acc_invert scrutinee in
        Array.fold_left
          (fun acc (_binder, constr) -> aux_constr acc constr)
          acc_scrutinee branches
    | Constr.Fix (_, (_names, types, bodies)) ->
        let acc_types = Array.fold_left aux_constr acc types in
        Array.fold_left aux_constr acc_types bodies
    | Constr.CoFix (_, (_names, types, bodies)) ->
        let acc_types = Array.fold_left aux_constr acc types in
        Array.fold_left aux_constr acc_types bodies
    | Constr.Proj (proj, _, c) ->
        aux_constr (Const (Names.Projection.constant proj) :: acc) c
    | Constr.Int _ -> acc
    | Constr.Float _ -> acc
    | Constr.String _ -> acc
    | Constr.Array (_, c_arr, c1, c2) ->
        let acc_arr = Array.fold_left aux_constr acc c_arr in
        let acc_c1 = aux_constr acc_arr c1 in
        aux_constr acc_c1 c2
  in
  let acc = aux_constr [] term in
  List_utils.dedup acc
