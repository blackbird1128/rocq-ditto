open Constrexpr

let option_to_list opt = match opt with Some x -> [ x ] | None -> []

let rec children_cases_pattern_expr (cp : cases_pattern_expr) =
  match cp.v with
  | CPatAlias (p, _) -> children_cases_pattern_expr p
  | CPatCstr (_, args_opt, args) ->
      let from_opt =
        match args_opt with
        | None -> []
        | Some ps -> List.concat_map children_cases_pattern_expr ps
      in
      from_opt @ List.concat_map children_cases_pattern_expr args
  | CPatOr ps -> List.concat_map children_cases_pattern_expr ps
  | CPatNotation (_, _, _, ps) -> List.concat_map children_cases_pattern_expr ps
  | CPatRecord fields ->
      List.concat_map (fun (_, p) -> children_cases_pattern_expr p) fields
  | CPatDelimiters (_, _, p) -> children_cases_pattern_expr p
  | CPatCast (p, e) -> e :: children_cases_pattern_expr p
  | CPatAtom _ | CPatPrim _ -> []

let children_local_binder_expr = function
  | CLocalAssum (_, _, _, ty) -> [ ty ]
  | CLocalDef (_, _, rhs, ty_opt) -> rhs :: option_to_list ty_opt
  | CLocalPattern _ -> []

let children_kinded_cases_pattern_expr (p, _) = children_cases_pattern_expr p

let children_constr_notation_substitution (es, ess, kps, lbs) =
  es @ List.concat ess
  @ List.concat_map children_kinded_cases_pattern_expr kps
  @ List.concat_map (List.concat_map children_local_binder_expr) lbs

let children_case_expr (scrut, _, pat_opt) =
  scrut
  :: (match pat_opt with None -> [] | Some p -> children_cases_pattern_expr p)

let children_branch_expr (b : branch_expr) =
  let pats, body = b.v in
  body :: List.concat_map (List.concat_map children_cases_pattern_expr) pats

let children_fixpoint_order_expr (fo : fixpoint_order_expr) =
  match fo.v with
  | CStructRec _ -> []
  | CWfRec (_, e) -> [ e ]
  | CMeasureRec (_, measure, rel_opt) -> measure :: option_to_list rel_opt

let children_fix_expr (_, _, order_opt, binders, body, ty) =
  (ty :: body :: List.concat_map children_local_binder_expr binders)
  @ match order_opt with None -> [] | Some o -> children_fixpoint_order_expr o

let children_cofix_expr (_, _, binders, body, ty) =
  ty :: body :: List.concat_map children_local_binder_expr binders

let children_constr_expr (ce : constr_expr) : constr_expr list =
  match ce.v with
  | CRef _ -> []
  | CFix (_, defs) -> List.concat_map children_fix_expr defs
  | CCoFix (_, defs) -> List.concat_map children_cofix_expr defs
  | CProdN (binders, body) | CLambdaN (binders, body) ->
      body :: List.concat_map children_local_binder_expr binders (* rec ok *)
  | CLetIn (_, rhs, ty_opt, body) ->
      rhs :: body :: (match ty_opt with Some t -> [ t ] | None -> [])
      (* rec ok *)
  | CAppExpl (_, args) -> args (* rec ok *)
  | CApp (fn, args) -> fn :: List.map fst args (* rec ok *)
  | CProj (_, _, args, scrut) -> scrut :: List.map fst args (* rec ok *)
  | CRecord fields -> List.map snd fields (* rec ok *)
  | CCases (_, ret_ty_opt, cases, branches) ->
      (* rec ok *)
      option_to_list ret_ty_opt
      @ List.concat_map children_case_expr cases
      @ List.concat_map children_branch_expr branches
  | CLetTuple (_, (_, ret_ty_opt), scrut, body) ->
      scrut :: body :: option_to_list ret_ty_opt (* rec ok *)
  | CIf (cond, (_, ret_ty_opt), then_, else_) ->
      cond :: then_ :: else_ :: option_to_list ret_ty_opt (* rec ok *)
  | CHole _ -> [] (* rec ok *)
  | CGenarg _ | CGenargGlob _ | CPatVar _ -> [] (* rec ok *)
  | CEvar (_, insts) -> List.map snd insts (* rec ok *)
  | CSort _ -> [] (* rec ok *)
  | CCast (e, _, ty) -> [ e; ty ] (* rec ok *)
  | CNotation (_, _, subst) ->
      children_constr_notation_substitution subst (* rec ok *)
  | CPrim _ -> [] (* rec ok *)
  | CGeneralization (_, e) | CDelimiters (_, _, e) -> [ e ] (* rec ok *)
  | CArray (_, arr, default, ty) -> Array.to_list arr @ [ default; ty ]

(* Rec ok *)

let rec fold_constr f acc ce =
  let acc = f ce acc in
  List.fold_left (fold_constr f) acc (children_constr_expr ce)

let exists (p : constr_expr -> bool) (ce : constr_expr) : bool =
  fold_constr (fun ce acc -> acc || p ce) false ce
