open Ltac_plugin

let get_raw_atomic_tactic_expr (x : Tacexpr.raw_tactic_expr) :
    Tacexpr.raw_atomic_tactic_expr option =
  match x.v with TacAtom expr -> Some expr | _ -> None

let default_extend_name : Vernacexpr.extend_name =
  {
    ext_plugin = Rocq_version.ltac_ext_plugin_name;
    ext_entry = "VernacSolve";
    ext_index = 0;
  }

open Ltac_plugin.Tacexpr
open CAst

type mapper = {
  map_expr : mapper -> raw_tactic_expr -> raw_tactic_expr;
  map_atom :
    mapper ->
    r_dispatch gen_atomic_tactic_expr ->
    r_dispatch gen_atomic_tactic_expr;
  map_arg : mapper -> r_dispatch gen_tactic_arg -> r_dispatch gen_tactic_arg;
}

let default_mapper : mapper =
  {
    map_expr =
      (fun self (expr : raw_tactic_expr) ->
        map
          (fun e ->
            match e with
            | TacAtom a -> TacAtom (self.map_atom self a)
            | TacThen (t1, t2) ->
                TacThen (self.map_expr self t1, self.map_expr self t2)
            | TacDispatch lst -> TacDispatch (List.map (self.map_expr self) lst)
            | TacExtendTac (pre, t, post) ->
                TacExtendTac
                  ( Array.map (self.map_expr self) pre,
                    self.map_expr self t,
                    Array.map (self.map_expr self) post )
            | TacThens (t, lst) ->
                TacThens
                  (self.map_expr self t, List.map (self.map_expr self) lst)
            | TacThens3parts (pre, a, mid, post) ->
                TacThens3parts
                  ( self.map_expr self pre,
                    Array.map (self.map_expr self) a,
                    self.map_expr self mid,
                    Array.map (self.map_expr self) post )
            | TacFirst lst -> TacFirst (List.map (self.map_expr self) lst)
            | TacSolve lst -> TacSolve (List.map (self.map_expr self) lst)
            | TacTry t -> TacTry (self.map_expr self t)
            | TacOr (t1, t2) ->
                TacOr (self.map_expr self t1, self.map_expr self t2)
            | TacIfThenCatch (a, b, c) ->
                TacIfThenCatch
                  ( self.map_expr self a,
                    self.map_expr self b,
                    self.map_expr self c )
            | TacOrelse (a, b) ->
                TacOrelse (self.map_expr self a, self.map_expr self b)
            | TacRepeat t -> TacRepeat (self.map_expr self t)
            | TacProgress t -> TacProgress (self.map_expr self t)
            | TacAbstract (t, name) -> TacAbstract (self.map_expr self t, name)
            | TacLetIn (recf, bindings, body) ->
                let bindings' =
                  List.map (fun (n, arg) -> (n, self.map_arg self arg)) bindings
                in
                TacLetIn (recf, bindings', self.map_expr self body)
            | TacMatch (lazyf, e, rules) ->
                let e' = self.map_expr self e in

                TacMatch (lazyf, e', rules)
            | TacMatchGoal (lazyf, dir, rules) ->
                TacMatchGoal (lazyf, dir, rules)
            | TacArg a -> TacArg (self.map_arg self a)
            | TacFun (args, body) -> TacFun (args, self.map_expr self body)
            | TacSelect (goal_select, expr) ->
                TacSelect (goal_select, self.map_expr self expr)
            | TacTimeout (timeout, tac) ->
                TacTimeout (timeout, self.map_expr self tac)
            | TacDo (x, y) -> TacDo (x, y)
            | TacTime (x, y) -> TacTime (x, y)
            | TacOnce tac -> TacOnce (self.map_expr self tac)
            | TacExactlyOnce tac -> TacExactlyOnce (self.map_expr self tac)
            (* the rest don’t recurse further *)
            | TacId _ | TacFail _ | TacML _ | TacAlias _ -> e)
          expr);
    map_atom =
      (fun self (a : r_dispatch gen_atomic_tactic_expr) ->
        match a with
        | TacApply (adv, ev, args, patterns) ->
            TacApply (adv, ev, args, patterns)
        | TacElim (ev, t, opt) -> TacElim (ev, t, opt)
        | TacRewrite (ev, lst, cl, tacopt) ->
            let tacopt' = Option.map (self.map_expr self) tacopt in
            TacRewrite (ev, lst, cl, tacopt')
        | TacAssert (ev, b, tacoptopt, ipat, trm) ->
            let tacoptopt' =
              Option.map (Option.map (self.map_expr self)) tacoptopt
            in
            TacAssert (ev, b, tacoptopt', ipat, trm)
        | _ -> a);
    map_arg =
      (fun self (a : r_dispatch gen_tactic_arg) ->
        match a with
        | Tacexp e -> Tacexp (self.map_expr self e)
        | TacCall c ->
            let c' =
              CAst.map
                (fun (r, args) -> (r, List.map (self.map_arg self) args))
                c
            in
            TacCall c'
        | _ -> a);
  }

let replace_fail_with_id =
  {
    default_mapper with
    map_expr =
      (fun self expr ->
        CAst.map
          (fun e ->
            match e with
            | TacFail _ -> TacId []
            | _ -> (default_mapper.map_expr self expr).v)
          expr);
  }
