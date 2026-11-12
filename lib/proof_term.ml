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
  | Constructor of Names.constructor

let collect_names (term : Constr.t) : name_ref list =
  let rec aux acc term =
    match Constr.kind term with
    | Constr.Rel _ -> acc
    | Constr.Var name -> Var name :: acc
    | Constr.Meta _ -> acc
    | Constr.Evar _ -> acc
    | Constr.Sort _ -> acc
    | Constr.Cast (init_term, _, end_term) ->
        let acc_init = aux acc init_term in
        aux acc_init end_term
    | Constr.Prod (_, c1, c2) ->
        let acc_c1 = aux acc c1 in
        aux acc_c1 c2
    | Constr.Lambda (_, c1, c2) ->
        let acc_c1 = aux acc c1 in
        aux acc_c1 c2
    | Constr.LetIn (_, c1, c2, c3) ->
        let acc_c1 = aux acc c1 in
        let acc_c2 = aux acc_c1 c2 in
        aux acc_c2 c3
    | Constr.App (app_constr, app_args) ->
        let acc_app = aux acc app_constr in
        Array.fold_left aux acc_app app_args
    | Constr.Const (c, _) -> Const c :: acc
    | Constr.Ind (ind, _) -> Inductive ind :: acc
    | Constr.Construct (cons, _) -> Constructor cons :: acc
    | Constr.Case (_, _, _, _, _, _, _) -> acc
    | Constr.Fix _ -> acc
    | Constr.CoFix _ -> acc
    | Constr.Proj (_, _, c) -> aux acc c
    | Constr.Int _ -> acc
    | Constr.Float _ -> acc
    | Constr.String _ -> acc
    | Constr.Array (_, c_arr, c1, c2) ->
        let acc_arr = Array.fold_left aux acc c_arr in
        let acc_c1 = aux acc_arr c1 in
        aux acc_c1 c2
  in
  aux [] term
