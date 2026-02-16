open Ltac_plugin

let map_match_pattern map_p = function
  | Tacexpr.Term x -> Tacexpr.Term (map_p x)
  | Tacexpr.Subterm (idopt, x) ->
      Tacexpr.Subterm (idopt, Constrexpr_map.constr_expr_map map_p x)

let map_match_context_hyps map_p = function
  | Tacexpr.Hyp (ln, p) -> Tacexpr.Hyp (ln, map_match_pattern map_p p)
  | Tacexpr.Def (ln, p1, p2) ->
      Tacexpr.Def (ln, map_match_pattern map_p p1, map_match_pattern map_p p2)

let rec tacexpr_fold_map_with_constr
    (step : 'acc -> Tacexpr.raw_tactic_expr -> 'acc)
    (f : Tacexpr.raw_tactic_expr -> Tacexpr.raw_tactic_expr)
    (g : Constrexpr.constr_expr -> Constrexpr.constr_expr) (acc : 'acc)
    (expr : Tacexpr.raw_tactic_expr) : 'acc * Tacexpr.raw_tactic_expr =
  let mk v = CAst.make ?loc:expr.loc v in

  (* recursive worker *)
  let fm = tacexpr_fold_map_with_constr step f g in

  let map1 acc x = fm acc x in

  let map_list acc xs =
    List.fold_right
      (fun x (acc, ys) ->
        let acc, x' = map1 acc x in
        (acc, x' :: ys))
      xs (acc, [])
  in

  let map_array acc a =
    (* preserve order; build list then array *)
    let acc, l' = map_list acc (Array.to_list a) in
    (acc, Array.of_list l')
  in

  let map_opt acc = function
    | None -> (acc, None)
    | Some x ->
        let acc, x' = map1 acc x in
        (acc, Some x')
  in

  let rec map_arg acc (arg : 'a Tacexpr.gen_tactic_arg) :
      'acc * 'a Tacexpr.gen_tactic_arg =
    match arg with
    | Tacexpr.TacGeneric _ -> (acc, arg)
    | Tacexpr.ConstrMayEval _ -> (acc, arg)
    | Tacexpr.Reference _ -> (acc, arg)
    | Tacexpr.TacFreshId _ -> (acc, arg)
    | Tacexpr.TacPretype _ -> (acc, arg)
    | Tacexpr.TacNumgoals -> (acc, arg)
    | Tacexpr.Tacexp t ->
        let acc, t' = map1 acc t in
        (acc, Tacexpr.Tacexp t')
    | Tacexpr.TacCall call ->
        let r, args = call.v in
        let acc, args' =
          List.fold_right
            (fun a (acc, xs) ->
              let acc, a' = map_arg acc a in
              (acc, a' :: xs))
            args (acc, [])
        in
        let call' = CAst.make ?loc:call.loc (r, args') in
        (acc, Tacexpr.TacCall call')
  in

  let map_atomic acc (a : 'a Tacexpr.gen_atomic_tactic_expr) :
      'acc * 'a Tacexpr.gen_atomic_tactic_expr =
    match a with
    | Tacexpr.TacIntroPattern _ -> (acc, a)
    | Tacexpr.TacApply _ -> (acc, a)
    | Tacexpr.TacElim _ -> (acc, a)
    | Tacexpr.TacCase _ -> (acc, a)
    | Tacexpr.TacMutualFix _ -> (acc, a)
    | Tacexpr.TacMutualCofix _ -> (acc, a)
    | Tacexpr.TacGeneralize _ -> (acc, a)
    | Tacexpr.TacLetTac _ -> (acc, a)
    | Tacexpr.TacInductionDestruct _ -> (acc, a)
    | Tacexpr.TacReduce _ -> (acc, a)
    | Tacexpr.TacChange _ -> (acc, a)
    | Tacexpr.TacInversion _ -> (acc, a)
    | Tacexpr.TacAssert (ev, b, tacoptopt, ipatopt, trm) ->
        let acc, tacoptopt' =
          match tacoptopt with
          | None -> (acc, None)
          | Some None -> (acc, Some None)
          | Some (Some t) ->
              let acc, t' = map1 acc t in
              (acc, Some (Some t'))
        in
        (acc, Tacexpr.TacAssert (ev, b, tacoptopt', ipatopt, trm))
    | Tacexpr.TacRewrite (ev, l, clause, tacopt) ->
        let acc, tacopt' = map_opt acc tacopt in
        (acc, Tacexpr.TacRewrite (ev, l, clause, tacopt'))
  in

  let acc, expr_mapped =
    match expr.v with
    | Tacexpr.TacAtom a ->
        let acc, a' = map_atomic acc a in
        (acc, mk (Tacexpr.TacAtom a'))
    | Tacexpr.TacThen (a, b) ->
        let acc, a' = map1 acc a in
        let acc, b' = map1 acc b in
        (acc, mk (Tacexpr.TacThen (a', b')))
    | Tacexpr.TacDispatch l ->
        let acc, l' = map_list acc l in
        (acc, mk (Tacexpr.TacDispatch l'))
    | Tacexpr.TacExtendTac (a1, t, a2) ->
        let acc, a1' = map_array acc a1 in
        let acc, t' = map1 acc t in
        let acc, a2' = map_array acc a2 in
        (acc, mk (Tacexpr.TacExtendTac (a1', t', a2')))
    | Tacexpr.TacThens (t, l) ->
        let acc, t' = map1 acc t in
        let acc, l' = map_list acc l in
        (acc, mk (Tacexpr.TacThens (t', l')))
    | Tacexpr.TacThens3parts (t1, a1, t2, a2) ->
        let acc, t1' = map1 acc t1 in
        let acc, a1' = map_array acc a1 in
        let acc, t2' = map1 acc t2 in
        let acc, a2' = map_array acc a2 in
        (acc, mk (Tacexpr.TacThens3parts (t1', a1', t2', a2')))
    | Tacexpr.TacFirst l ->
        let acc, l' = map_list acc l in
        (acc, mk (Tacexpr.TacFirst l'))
    | Tacexpr.TacSolve l ->
        let acc, l' = map_list acc l in
        (acc, mk (Tacexpr.TacSolve l'))
    | Tacexpr.TacTry t ->
        let acc, t' = map1 acc t in
        (acc, mk (Tacexpr.TacTry t'))
    | Tacexpr.TacOr (a, b) ->
        let acc, a' = map1 acc a in
        let acc, b' = map1 acc b in
        (acc, mk (Tacexpr.TacOr (a', b')))
    | Tacexpr.TacOnce t ->
        let acc, t' = map1 acc t in
        (acc, mk (Tacexpr.TacOnce t'))
    | Tacexpr.TacExactlyOnce t ->
        let acc, t' = map1 acc t in
        (acc, mk (Tacexpr.TacExactlyOnce t'))
    | Tacexpr.TacIfThenCatch (a, b, c) ->
        let acc, a' = map1 acc a in
        let acc, b' = map1 acc b in
        let acc, c' = map1 acc c in
        (acc, mk (Tacexpr.TacIfThenCatch (a', b', c')))
    | Tacexpr.TacOrelse (a, b) ->
        let acc, a' = map1 acc a in
        let acc, b' = map1 acc b in
        (acc, mk (Tacexpr.TacOrelse (a', b')))
    | Tacexpr.TacDo (n, t) ->
        let acc, t' = map1 acc t in
        (acc, mk (Tacexpr.TacDo (n, t')))
    | Tacexpr.TacTimeout (n, t) ->
        let acc, t' = map1 acc t in
        (acc, mk (Tacexpr.TacTimeout (n, t')))
    | Tacexpr.TacTime (s, t) ->
        let acc, t' = map1 acc t in
        (acc, mk (Tacexpr.TacTime (s, t')))
    | Tacexpr.TacRepeat t ->
        let acc, t' = map1 acc t in
        (acc, mk (Tacexpr.TacRepeat t'))
    | Tacexpr.TacProgress t ->
        let acc, t' = map1 acc t in
        (acc, mk (Tacexpr.TacProgress t'))
    | Tacexpr.TacAbstract (t, nameopt) ->
        let acc, t' = map1 acc t in
        (acc, mk (Tacexpr.TacAbstract (t', nameopt)))
    | Tacexpr.TacId _ | TacFail _ -> (acc, expr)
    | Tacexpr.TacLetIn (rf, binds, body) ->
        let acc, binds' =
          List.fold_right
            (fun (ln, a) (acc, xs) ->
              let acc, a' = map_arg acc a in
              (acc, (ln, a') :: xs))
            binds (acc, [])
        in
        let acc, body' = map1 acc body in
        (acc, mk (Tacexpr.TacLetIn (rf, binds', body')))
    | Tacexpr.TacMatch (lf, scrut, rules) ->
        let acc, scrut' = map1 acc scrut in
        (* rules don't contain tactics except `t`; we still need to thread acc through `t` *)
        let acc, rules' =
          List.fold_right
            (fun rule (acc, xs) ->
              match rule with
              | Tacexpr.All t ->
                  let acc, t' = map1 acc t in
                  (acc, Tacexpr.All t' :: xs)
              | Tacexpr.Pat (hyps, pat, t) ->
                  let acc, t' = map1 acc t in
                  let hyps' = List.map (map_match_context_hyps g) hyps in
                  let pat' = map_match_pattern g pat in
                  (acc, Tacexpr.Pat (hyps', pat', t') :: xs))
            rules (acc, [])
        in
        (acc, mk (Tacexpr.TacMatch (lf, scrut', rules')))
    | Tacexpr.TacMatchGoal (lf, dir, rules) ->
        let acc, rules' =
          List.fold_right
            (fun rule (acc, xs) ->
              match rule with
              | Tacexpr.All t ->
                  let acc, t' = map1 acc t in
                  (acc, Tacexpr.All t' :: xs)
              | Tacexpr.Pat (hyps, pat, t) ->
                  let acc, t' = map1 acc t in
                  let hyps' = List.map (map_match_context_hyps g) hyps in
                  let pat' = map_match_pattern g pat in
                  (acc, Tacexpr.Pat (hyps', pat', t') :: xs))
            rules (acc, [])
        in
        (acc, mk (Tacexpr.TacMatchGoal (lf, dir, rules')))
    | Tacexpr.TacFun (names, body) ->
        let acc, body' = map1 acc body in
        (acc, mk (Tacexpr.TacFun (names, body')))
    | Tacexpr.TacArg a ->
        let acc, a' = map_arg acc a in
        (acc, mk (Tacexpr.TacArg a'))
    | Tacexpr.TacSelect (gs, t) ->
        let acc, t' = map1 acc t in
        (acc, mk (Tacexpr.TacSelect (gs, t')))
    | Tacexpr.TacML (entry, args) ->
        let acc, args' =
          List.fold_right
            (fun a (acc, xs) ->
              let acc, a' = map_arg acc a in
              (acc, a' :: xs))
            args (acc, [])
        in
        (acc, mk (Tacexpr.TacML (entry, args')))
    | Tacexpr.TacAlias (kn, args) ->
        let acc, args' =
          List.fold_right
            (fun a (acc, xs) ->
              let acc, a' = map_arg acc a in
              (acc, a' :: xs))
            args (acc, [])
        in
        (acc, mk (Tacexpr.TacAlias (kn, args')))
  in

  (* Bottom-up: apply user map `f` after children are mapped *)
  let expr' = f expr_mapped in

  (* Fold step: decide whether to fold on original or mapped node.
     Typically: fold on mapped node (expr') in bottom-up traversals. *)
  let acc' = step acc expr' in
  (acc', expr')

let tacexpr_map_with_constr
    (f : Tacexpr.raw_tactic_expr -> Tacexpr.raw_tactic_expr)
    (g : Constrexpr.constr_expr -> Constrexpr.constr_expr)
    (expr : Tacexpr.raw_tactic_expr) : Tacexpr.raw_tactic_expr =
  snd (tacexpr_fold_map_with_constr (fun acc _ -> acc) f g () expr)

let tacexpr_map (f : Tacexpr.raw_tactic_expr -> Tacexpr.raw_tactic_expr)
    (expr : Tacexpr.raw_tactic_expr) : Tacexpr.raw_tactic_expr =
  tacexpr_map_with_constr f Fun.id expr

let tacexpr_fold (step : 'acc -> Tacexpr.raw_tactic_expr -> 'acc) (acc : 'acc)
    (expr : Tacexpr.raw_tactic_expr) : 'acc =
  fst (tacexpr_fold_map_with_constr step Fun.id Fun.id acc expr)

(* let eq_node (x : Tacexpr.raw_tactic_expr) (y : Tacexpr.raw_tactic_expr) = x == y *)
let mk ?loc v : Tacexpr.raw_tactic_expr = CAst.make ?loc v
let mk_idtac ?loc () : Tacexpr.raw_tactic_expr = mk ?loc (Tacexpr.TacId [])

let is_idtac (e : Tacexpr.raw_tactic_expr) =
  match e.v with Tacexpr.TacId _ -> true | _ -> false

let rec simplify (e : Tacexpr.raw_tactic_expr) : Tacexpr.raw_tactic_expr =
  match e.v with
  | Tacexpr.TacThen (a, b) ->
      let a = simplify a in
      let b = simplify b in
      if is_idtac a then b
      else if is_idtac b then a
      else mk ?loc:e.loc (Tacexpr.TacThen (a, b))
  | Tacexpr.TacThens (t, branches) ->
      let t = simplify t in
      let branches = List.map simplify branches in
      if List.for_all is_idtac branches then t
      else mk ?loc:e.loc (Tacexpr.TacThens (t, branches))
  | _ -> e

(* Only these are "transparent" scheduling reasoning right now. *)
let is_transparent_for_schedule (e : Tacexpr.raw_tactic_expr) : bool =
  match e.v with
  | Tacexpr.TacThen _ -> true
  | Tacexpr.TacThens _ -> true
  | _ -> false

type hit =
  | Before (* stop right before target: idtac *)
  | Include (* include the target itself *)

(** Return an expression that, when executed, leaves the context in the same
    state as the original would *just before executing [target] in [e] if [hit]
    is [Before] and after executing [target] if [hit] is [Include]*. Returns
    None if [target] is not found (or is inside an opaque tactic). *)
let rec prefix_until ~(hit : hit)
    ~(eq : Tacexpr.raw_tactic_expr -> Tacexpr.raw_tactic_expr -> bool)
    ~(target : Tacexpr.raw_tactic_expr) (e : Tacexpr.raw_tactic_expr) :
    Tacexpr.raw_tactic_expr option =
  if eq e target then
    Some (match hit with Before -> mk_idtac ?loc:e.loc () | Include -> e)
  else if not (is_transparent_for_schedule e) then None
  else
    match e.v with
    | Tacexpr.TacThen (a, b) -> begin
        match prefix_until ~hit ~eq ~target a with
        | Some pre_a ->
            (* We’re still “in a”: b hasn’t started yet *)
            Some
              (mk ?loc:e.loc (Tacexpr.TacThen (pre_a, mk_idtac ?loc:e.loc ()))
              |> simplify)
        | None ->
            (* Not in a => must be in b *)
            begin match prefix_until ~hit ~eq ~target b with
            | Some pre_b ->
                Some (mk ?loc:e.loc (Tacexpr.TacThen (a, pre_b)) |> simplify)
            | None -> None
            end
      end
    | Tacexpr.TacThens (t, branches) -> (
        match prefix_until ~hit ~eq ~target t with
        | Some pre_t ->
            let holes = List.map (fun _ -> mk_idtac ?loc:e.loc ()) branches in
            Some (mk ?loc:e.loc (Tacexpr.TacThens (pre_t, holes)) |> simplify)
        | None -> (
            let rec find i = function
              | [] -> None
              | bi :: bs -> (
                  if eq bi target then
                    Some
                      ( i,
                        match hit with
                        | Before -> mk_idtac ?loc:e.loc ()
                        | Include -> bi )
                  else
                    match prefix_until ~hit ~eq ~target bi with
                    | Some pre_bi -> Some (i, pre_bi)
                    | None -> find (i + 1) bs)
            in
            match find 0 branches with
            | None -> None
            | Some (k, pre_k) ->
                let branches' =
                  List.mapi
                    (fun i _ -> if i = k then pre_k else mk_idtac ?loc:e.loc ())
                    branches
                in
                Some
                  (mk ?loc:e.loc (Tacexpr.TacThens (t, branches')) |> simplify))
        )
    | _ -> None

let prefix_before ~eq ~target e = prefix_until ~hit:Before ~eq ~target e
let prefix_including ~eq ~target e = prefix_until ~hit:Include ~eq ~target e
