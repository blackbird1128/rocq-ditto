let rec constr_expr_map (m : Constrexpr.constr_expr -> Constrexpr.constr_expr)
    (term : Constrexpr.constr_expr) : Constrexpr.constr_expr * bool =
  let open Constrexpr in
  let recurse = constr_expr_map m in
  let default t = m t in
  let new_term =
    match term.v with
    | CRef _ | CFix _ | CCoFix _ | CAppExpl _ | CProj _ | CRecord _ | CCases _
    | CLetTuple _ | CIf _ | CHole _ | CGenarg _ | CGenargGlob _ | CPatVar _
    | CEvar _ | CSort _ | CGeneralization _ | CPrim _ | CDelimiters _ | CArray _
      ->
        default term
    | CProdN (binders, expr) ->
        let expr', _ = recurse expr in
        default (CAst.make (CProdN (binders, expr')))
    | CLambdaN (binders, expr) ->
        let expr', _ = recurse expr in
        default (CAst.make (CLambdaN (binders, expr')))
    | CLetIn (name, expr, expr_opt, expr_bis) ->
        let expr', _ = recurse expr in
        let expr_opt' = Option.map (fun e -> fst (recurse e)) expr_opt in
        let expr_bis', _ = recurse expr_bis in
        default (CAst.make (CLetIn (name, expr', expr_opt', expr_bis')))
    | CApp (f, args) ->
        let f', _ = recurse f in
        default (CAst.make (CApp (f', args)))
    | CCast (from, kind, to_) ->
        let from', _ = recurse from in
        let to_', _ = recurse to_ in
        default (CAst.make (CCast (from', kind, to_')))
    | CNotation (scope, (entry, key), (l1, ll, pat, binders)) ->
        let l1' = List.map (fun e -> fst (recurse e)) l1 in
        default
          (CAst.make (CNotation (scope, (entry, key), (l1', ll, pat, binders))))
  in
  (new_term, not (Constrexpr_ops.constr_expr_eq new_term term))
