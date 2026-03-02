let constrexpr_to_string (x : Constrexpr.constr_expr) : string =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let pp = Ppconstr.pr_constr_expr env sigma x in
  Pp.string_of_ppcmds pp

let get_cref_qualid (x : Constrexpr.constr_expr) : Libnames.qualid option =
  match x.v with Constrexpr.CRef (qualid, _) -> Some qualid | _ -> None

let rec get_fun_name_in_constrexpr (term : Constrexpr.constr_expr) :
    Libnames.qualid option =
  match term.v with
  | Constrexpr.CRef (q, _) -> Some q
  | Constrexpr.CApp (func, _) -> get_fun_name_in_constrexpr func
  | Constrexpr.CAppExpl ((q, _), _) -> Some q
  | _ -> None

let get_fun_names_in_constrexpr (term : Constrexpr.constr_expr) :
    Libnames.qualid list =
  Constrexpr_fold.fold
    (fun x acc ->
      match get_fun_name_in_constrexpr x with
      | Some qualid -> qualid :: acc
      | None -> acc)
    [] term

let get_func_args (x : Constrexpr.constr_expr) : Constrexpr.constr_expr list =
  match x.v with Constrexpr.CApp (_, args) -> List.map fst args | _ -> []

let is_constrexpr_c_app_named (x : Constrexpr.constr_expr) (name : string) :
    bool =
  match x.v with
  | Constrexpr.CApp (func, _) ->
      Option.map Libnames.string_of_qualid (get_cref_qualid func) = Some name
  | _ -> false
