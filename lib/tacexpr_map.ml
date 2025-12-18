open Ltac_plugin

let rec tacexpr_map
    (f : 'a Tacexpr.gen_tactic_expr -> 'a Tacexpr.gen_tactic_expr)
    (expr : 'a Tacexpr.gen_tactic_expr) : 'a Tacexpr.gen_tactic_expr =
  let map = tacexpr_map f in
  let map_list = List.map map in
  let map_array = Array.map map in
  let map_opt = Option.map map in
  let mk v = CAst.make ?loc:expr.loc v in

  let rec map_arg (arg : 'a Tacexpr.gen_tactic_arg) : 'a Tacexpr.gen_tactic_arg
      =
    match arg with
    | Tacexpr.TacGeneric _ -> arg
    | Tacexpr.ConstrMayEval _ -> arg
    | Tacexpr.Reference _ -> arg
    | Tacexpr.TacFreshId _ -> arg
    | Tacexpr.TacPretype _ -> arg
    | Tacexpr.TacNumgoals -> arg
    | Tacexpr.Tacexp t -> Tacexpr.Tacexp (map t)
    | Tacexpr.TacCall call ->
        let r, args = call.v in
        CAst.make ?loc:call.loc (r, List.map map_arg args) |> fun call' ->
        Tacexpr.TacCall call'
  in

  let map_atomic (a : 'a Tacexpr.gen_atomic_tactic_expr) :
      'a Tacexpr.gen_atomic_tactic_expr =
    match a with
    | Tacexpr.TacIntroPattern _ -> a
    | Tacexpr.TacApply _ -> a
    | Tacexpr.TacElim _ -> a
    | Tacexpr.TacCase _ -> a
    | Tacexpr.TacMutualFix _ -> a
    | Tacexpr.TacMutualCofix _ -> a
    | Tacexpr.TacGeneralize _ -> a
    | Tacexpr.TacLetTac _ -> a
    | Tacexpr.TacInductionDestruct _ -> a
    | Tacexpr.TacReduce _ -> a
    | Tacexpr.TacChange _ -> a
    | Tacexpr.TacInversion _ -> a
    | Tacexpr.TacAssert (ev, b, tacoptopt, ipatopt, trm) ->
        let tacoptopt' = Option.map (Option.map map) tacoptopt in
        Tacexpr.TacAssert (ev, b, tacoptopt', ipatopt, trm)
    | Tacexpr.TacRewrite (ev, l, clause, tacopt) ->
        let tacopt' = map_opt tacopt in
        Tacexpr.TacRewrite (ev, l, clause, tacopt')
  in

  let expr' =
    match expr.v with
    | Tacexpr.TacAtom a -> mk (Tacexpr.TacAtom (map_atomic a))
    | Tacexpr.TacThen (a, b) -> mk (Tacexpr.TacThen (map a, map b))
    | Tacexpr.TacDispatch l -> mk (Tacexpr.TacDispatch (map_list l))
    | Tacexpr.TacExtendTac (a1, t, a2) ->
        mk (Tacexpr.TacExtendTac (map_array a1, map t, map_array a2))
    | Tacexpr.TacThens (t, l) -> mk (Tacexpr.TacThens (map t, map_list l))
    | Tacexpr.TacThens3parts (t1, a1, t2, a2) ->
        mk (Tacexpr.TacThens3parts (map t1, map_array a1, map t2, map_array a2))
    | Tacexpr.TacFirst l -> mk (Tacexpr.TacFirst (map_list l))
    | Tacexpr.TacSolve l -> mk (Tacexpr.TacSolve (map_list l))
    | Tacexpr.TacTry t -> mk (Tacexpr.TacTry (map t))
    | Tacexpr.TacOr (a, b) -> mk (Tacexpr.TacOr (map a, map b))
    | Tacexpr.TacOnce t -> mk (Tacexpr.TacOnce (map t))
    | Tacexpr.TacExactlyOnce t -> mk (Tacexpr.TacExactlyOnce (map t))
    | Tacexpr.TacIfThenCatch (a, b, c) ->
        mk (Tacexpr.TacIfThenCatch (map a, map b, map c))
    | Tacexpr.TacOrelse (a, b) -> mk (Tacexpr.TacOrelse (map a, map b))
    | Tacexpr.TacDo (n, t) -> mk (Tacexpr.TacDo (n, map t))
    | Tacexpr.TacTimeout (n, t) -> mk (Tacexpr.TacTimeout (n, map t))
    | Tacexpr.TacTime (s, t) -> mk (Tacexpr.TacTime (s, map t))
    | Tacexpr.TacRepeat t -> mk (Tacexpr.TacRepeat (map t))
    | Tacexpr.TacProgress t -> mk (Tacexpr.TacProgress (map t))
    | Tacexpr.TacAbstract (t, nameopt) ->
        mk (Tacexpr.TacAbstract (map t, nameopt))
    | Tacexpr.TacId _ -> expr
    | Tacexpr.TacFail _ -> expr
    | Tacexpr.TacLetIn (rf, binds, body) ->
        let binds' = List.map (fun (ln, a) -> (ln, map_arg a)) binds in
        mk (Tacexpr.TacLetIn (rf, binds', map body))
    | Tacexpr.TacMatch (lf, scrut, rules) ->
        mk (Tacexpr.TacMatch (lf, map scrut, rules))
    | Tacexpr.TacMatchGoal (lf, dir, rules) -> expr
    | Tacexpr.TacFun (names, body) -> mk (Tacexpr.TacFun (names, map body))
    | Tacexpr.TacArg a -> mk (Tacexpr.TacArg (map_arg a))
    | Tacexpr.TacSelect (gs, t) -> mk (Tacexpr.TacSelect (gs, map t))
    | Tacexpr.TacML (entry, args) ->
        mk (Tacexpr.TacML (entry, List.map map_arg args))
    | Tacexpr.TacAlias (kn, args) ->
        mk (Tacexpr.TacAlias (kn, List.map map_arg args))
  in

  (* bottom-up: apply user function after mapping children *)
  f expr'
