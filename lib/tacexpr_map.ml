open Ltac_plugin

let rec tacexpr_map (m : Tacexpr.raw_tactic_expr -> Tacexpr.raw_tactic_expr)
    (expr : Tacexpr.raw_tactic_expr) : Tacexpr.raw_tactic_expr * bool =
  let recurse =
   fun x ->
    let res, _ = tacexpr_map m x in
    res
  in
  let default t = m t in
  let new_expr =
    match expr.v with
    | Tacexpr.TacAtom _ -> default expr
    | Tacexpr.TacThen (a, b) ->
        let a' = recurse a in
        let b' = recurse b in
        default (CAst.make (Tacexpr.TacThen (a', b')))
    | Tacexpr.TacDispatch tacexpr_list ->
        let mapped_l = List.map recurse tacexpr_list in
        default (CAst.make (Tacexpr.TacDispatch mapped_l))
    | Tacexpr.TacExtendTac (tacexpr_array1, tacexpr, tacexpr_array2) ->
        let mapped_a1 = Array.map recurse tacexpr_array1 in
        let mapped_tacexpr = recurse tacexpr in
        let mapped_a2 = Array.map recurse tacexpr_array2 in
        default
          (CAst.make
             (Tacexpr.TacExtendTac (mapped_a1, mapped_tacexpr, mapped_a2)))
    | Tacexpr.TacThens (tacexpr, tacexpr_list) ->
        let tacexpr_mapped = recurse tacexpr in
        let mapped_l = List.map recurse tacexpr_list in
        default (CAst.make (Tacexpr.TacThens (tacexpr_mapped, mapped_l)))
    | Tacexpr.TacThens3parts (_, _, _, _) -> default expr
    | Tacexpr.TacFirst tacexpr_list ->
        let mapped_l = List.map recurse tacexpr_list in
        default (CAst.make (Tacexpr.TacFirst mapped_l))
    | Tacexpr.TacSolve tacexpr_list ->
        let mapped_l = List.map recurse tacexpr_list in
        default (CAst.make (Tacexpr.TacSolve mapped_l))
    | Tacexpr.TacTry a ->
        let a' = recurse a in
        default (CAst.make (Tacexpr.TacTry a'))
    | Tacexpr.TacOr (a, b) ->
        let a' = recurse a in
        let b' = recurse b in
        default (CAst.make (Tacexpr.TacOr (a', b')))
    | Tacexpr.TacOnce tacexpr ->
        let mapped_tacexpr = recurse tacexpr in
        default (CAst.make (Tacexpr.TacOnce mapped_tacexpr))
    | Tacexpr.TacExactlyOnce tacexpr ->
        let mapped_tacexpr = recurse tacexpr in
        default (CAst.make (Tacexpr.TacExactlyOnce mapped_tacexpr))
    | Tacexpr.TacIfThenCatch (_, _, _) -> default expr
    | Tacexpr.TacOrelse (a, b) ->
        let a' = recurse a in
        let b' = recurse b in
        default (CAst.make (Tacexpr.TacOrelse (a', b')))
    | Tacexpr.TacDo (n, tacexpr) ->
        let mapped_tacexpr = recurse tacexpr in
        default (CAst.make (Tacexpr.TacDo (n, mapped_tacexpr)))
    | Tacexpr.TacTimeout (n, tacexpr) ->
        let mapped_tacexpr = recurse tacexpr in
        default (CAst.make (Tacexpr.TacTimeout (n, mapped_tacexpr)))
    | Tacexpr.TacTime (opt_str, tacexpr) ->
        let mapped_tacexpr = recurse tacexpr in
        default (CAst.make (Tacexpr.TacTime (opt_str, mapped_tacexpr)))
    | Tacexpr.TacRepeat tacexpr ->
        let mapped_tacexpr = recurse tacexpr in
        default (CAst.make (Tacexpr.TacRepeat mapped_tacexpr))
    | Tacexpr.TacProgress tacexpr ->
        let mapped_tacexpr = recurse tacexpr in
        default (CAst.make (Tacexpr.TacProgress mapped_tacexpr))
    | Tacexpr.TacAbstract (tacexpr, opt_name) ->
        let mapped_tacexpr = recurse tacexpr in
        default (CAst.make (Tacexpr.TacAbstract (mapped_tacexpr, opt_name)))
    | Tacexpr.TacId _ | Tacexpr.TacFail (_, _, _) -> default expr
    | Tacexpr.TacLetIn (_, _, _) -> default expr
    | Tacexpr.TacMatch (_, _, _) -> default expr
    | Tacexpr.TacMatchGoal (_, _, _) -> default expr
    | Tacexpr.TacFun _ -> default expr
    | Tacexpr.TacArg tacexpr -> default expr
    | Tacexpr.TacSelect (goal_select, tacexpr) ->
        let mapped_tacexpr = recurse tacexpr in
        default (CAst.make (Tacexpr.TacSelect (goal_select, mapped_tacexpr)))
    | Tacexpr.TacML (_, _) -> default expr
    | Tacexpr.TacAlias (ltac_constant, tacexpr_list) -> default expr
  in
  (new_expr, expr != new_expr)
