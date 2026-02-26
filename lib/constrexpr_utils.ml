let constrexpr_to_string (x : Constrexpr.constr_expr) : string =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let pp = Ppconstr.pr_constr_expr env sigma x in
  Pp.string_of_ppcmds pp

let get_cref_qualid (x : Constrexpr.constr_expr) : Libnames.qualid option =
  match x.v with Constrexpr.CRef (qualid, _) -> Some qualid | _ -> None

let get_func_args (x : Constrexpr.constr_expr) : Constrexpr.constr_expr list =
  match x.v with Constrexpr.CApp (_, args) -> List.map fst args | _ -> []
