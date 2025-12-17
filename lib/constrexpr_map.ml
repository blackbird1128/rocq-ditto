open Constrexpr

let option_map f = function None -> None | Some x -> Some (f x)

let rec cases_pattern_expr_map m (cp : cases_pattern_expr) =
  let v =
    match cp.v with
    | CPatAlias (p, id) -> CPatAlias (cases_pattern_expr_map m p, id)
    | CPatCstr (c, args_opt, args) ->
        CPatCstr
          ( c,
            option_map (List.map (cases_pattern_expr_map m)) args_opt,
            List.map (cases_pattern_expr_map m) args )
    | CPatOr ps -> CPatOr (List.map (cases_pattern_expr_map m) ps)
    | CPatNotation (s, a, b, ps) ->
        CPatNotation (s, a, b, List.map (cases_pattern_expr_map m) ps)
    | CPatRecord fields ->
        CPatRecord
          (List.map (fun (l, p) -> (l, cases_pattern_expr_map m p)) fields)
    | CPatDelimiters (a, b, p) ->
        CPatDelimiters (a, b, cases_pattern_expr_map m p)
    | CPatCast (p, e) ->
        CPatCast (cases_pattern_expr_map m p, constr_expr_map m e)
    | CPatAtom _ | CPatPrim _ -> cp.v
  in
  v |> CAst.make

and local_binder_expr_map m = function
  | CLocalAssum (ids, k, b, ty) -> CLocalAssum (ids, k, b, constr_expr_map m ty)
  | CLocalDef (id, k, rhs, ty_opt) ->
      CLocalDef
        (id, k, constr_expr_map m rhs, option_map (constr_expr_map m) ty_opt)
  | CLocalPattern _ as lb -> lb

and fixpoint_order_expr_map m (fo : fixpoint_order_expr) =
  let (v : fixpoint_order_expr_r) =
    match fo.v with
    | CStructRec _ -> fo.v
    | CWfRec (id, e) -> CWfRec (id, constr_expr_map m e)
    | CMeasureRec (id, measure, rel_opt) ->
        CMeasureRec
          (id, constr_expr_map m measure, option_map (constr_expr_map m) rel_opt)
  in
  v |> CAst.make

and constr_expr_map (m : Constrexpr.constr_expr -> Constrexpr.constr_expr)
    (term : Constrexpr.constr_expr) : Constrexpr.constr_expr =
  let res =
    match term.v with
    | CRef _ -> term.v
    | CFix (k, defs) ->
        CFix
          ( k,
            List.map
              (fun (id, bl, ord_opt, binders, body, ty) ->
                ( id,
                  bl,
                  option_map (fixpoint_order_expr_map m) ord_opt,
                  List.map (local_binder_expr_map m) binders,
                  constr_expr_map m body,
                  constr_expr_map m ty ))
              defs )
    | CCoFix (k, defs) ->
        CCoFix
          ( k,
            List.map
              (fun (id, bl, binders, body, ty) ->
                ( id,
                  bl,
                  List.map (local_binder_expr_map m) binders,
                  constr_expr_map m body,
                  constr_expr_map m ty ))
              defs )
    | CProdN (binders, body) ->
        CProdN
          (List.map (local_binder_expr_map m) binders, constr_expr_map m body)
    | CLambdaN (binders, body) ->
        CLambdaN
          (List.map (local_binder_expr_map m) binders, constr_expr_map m body)
    | CLetIn (id, rhs, ty_opt, body) ->
        CLetIn
          ( id,
            constr_expr_map m rhs,
            option_map (constr_expr_map m) ty_opt,
            constr_expr_map m body )
    | CAppExpl (f, args) -> CAppExpl (f, List.map (constr_expr_map m) args)
    | CApp (fn, args) ->
        CApp
          ( constr_expr_map m fn,
            List.map (fun (e, i) -> (constr_expr_map m e, i)) args )
    | CProj (p, q, args, scrut) ->
        CProj
          ( p,
            q,
            List.map (fun (e, i) -> (constr_expr_map m e, i)) args,
            constr_expr_map m scrut )
    | CRecord fields ->
        CRecord (List.map (fun (l, e) -> (l, constr_expr_map m e)) fields)
    | CCases (sty, ret_ty_opt, cases, branches) ->
        CCases
          ( sty,
            option_map (constr_expr_map m) ret_ty_opt,
            List.map
              (fun (scrut, k, pat_opt) -> (constr_expr_map m scrut, k, pat_opt))
              cases,
            List.map
              (fun (b : branch_expr) ->
                let pats, body = b.v in

                ( List.map (List.map (cases_pattern_expr_map m)) pats,
                  constr_expr_map m body )
                |> CAst.make)
              branches )
    | CLetTuple (ids, (na, ret_ty_opt), scrut, body) ->
        CLetTuple
          ( ids,
            (na, option_map (constr_expr_map m) ret_ty_opt),
            constr_expr_map m scrut,
            constr_expr_map m body )
    | CIf (cond, (na, ret_ty_opt), then_, else_) ->
        CIf
          ( constr_expr_map m cond,
            (na, option_map (constr_expr_map m) ret_ty_opt),
            constr_expr_map m then_,
            constr_expr_map m else_ )
    | CEvar (k, insts) ->
        CEvar (k, List.map (fun (id, e) -> (id, constr_expr_map m e)) insts)
    | CCast (e, k, ty) -> CCast (constr_expr_map m e, k, constr_expr_map m ty)
    | CNotation (s, a, (es, ess, kps, lbs)) ->
        CNotation
          ( s,
            a,
            ( List.map (constr_expr_map m) es,
              List.map (List.map (constr_expr_map m)) ess,
              List.map (fun (p, k) -> (cases_pattern_expr_map m p, k)) kps,
              List.map (List.map (local_binder_expr_map m)) lbs ) )
    | CGeneralization (k, e) -> CGeneralization (k, constr_expr_map m e)
    | CDelimiters (a, b, e) -> CDelimiters (a, b, constr_expr_map m e)
    | CArray (k, arr, default, ty) ->
        CArray
          ( k,
            Array.map (constr_expr_map m) arr,
            constr_expr_map m default,
            constr_expr_map m ty )
    | CHole _ | CGenarg _ | CGenargGlob _ | CPatVar _ | CSort _ | CPrim _ ->
        term.v
  in

  m (res |> CAst.make)
