open Fleche
open Ditto
open Ditto.Proof_tree
open Ditto.Proof
open Ditto.Syntax_node
open Vernacexpr
open Theorem_query

let wrap_to_treeify doc x = Result.get_ok (Runner.treeify_proof doc x)

let error_location_to_string (location : Lang.Range.t) : string =
  if location.start.line = location.end_.line then
    "line "
    ^ string_of_int location.start.line
    ^ ", characters: "
    ^ string_of_int location.start.character
    ^ "-"
    ^ string_of_int location.end_.character
  else
    "line "
    ^ string_of_int location.start.line
    ^ "-"
    ^ string_of_int location.end_.line
    ^ ", characters: "
    ^ string_of_int location.start.character
    ^ "-"
    ^ string_of_int location.end_.character

let diagnostic_kind_to_str (diag_kind : Lang.Diagnostic.Severity.t) : string =
  if diag_kind = Lang.Diagnostic.Severity.error then "Error"
  else if diag_kind = Lang.Diagnostic.Severity.hint then "Hint"
  else if diag_kind = Lang.Diagnostic.Severity.information then "Information"
  else "Warning"

let print_diagnostics (errors : Lang.Diagnostic.t list) : unit =
  List.iter
    (fun (diag : Lang.Diagnostic.t) ->
      print_endline
        ("At: "
        ^ error_location_to_string diag.range
        ^ " "
        ^ diagnostic_kind_to_str diag.severity
        ^ ": "
        ^ Pp.string_of_ppcmds diag.message))
    errors

let remove_loc sexp =
  let open Sexplib.Sexp in
  let rec aux sexp =
    match sexp with
    | Atom _ -> sexp
    | List (Atom "loc" :: _) -> List [] (* or List [] *)
    | List l ->
        let filtered =
          List.filter_map
            (fun s ->
              match s with List (Atom "loc" :: _) -> None | _ -> Some (aux s))
            l
        in
        List filtered
  in
  aux sexp

let print_prim_token (x : Constrexpr.prim_token) =
  match x with
  | Constrexpr.Number num -> print_endline (NumTok.Signed.to_string num)
  | Constrexpr.String string -> print_endline string

let print_lident (x : Names.lident) = print_endline (Names.Id.to_string x.v)

let print_qualid (x : Libnames.qualid) =
  print_endline (Libnames.string_of_qualid x)

let print_binder_type (x : Constrexpr.local_binder_expr) =
  match x with
  | Constrexpr.CLocalAssum
      (lnames, relevance_info_expr, binder_kind, constr_expr) ->
      print_endline "assum kind (forall ?)"
  | Constrexpr.CLocalDef (_, _, _, _) -> print_endline "local def kind "
  | Constrexpr.CLocalPattern _ -> print_endline "local pattern kind"

let rec print_info_constr_expr (x : Constrexpr.constr_expr) =
  Pp.pp_with Format.std_formatter (Loc.pr (Option.get x.loc));
  Format.print_newline ();
  match x.v with
  | Constrexpr.CRef (qualid, instance_expr) -> (
      print_endline "yep that a ref";
      print_qualid qualid;
      match instance_expr with
      | Some _ -> print_endline "Ho god we have an instance expr ! Panic !!"
      | None -> print_endline "all good boss")
  | Constrexpr.CFix (_, _) -> print_endline "not handled"
  | Constrexpr.CCoFix (_, _) -> print_endline "not handled"
  | Constrexpr.CProdN (binders, expr) ->
      List.iter print_binder_type binders;
      print_info_constr_expr expr
  | Constrexpr.CLambdaN (_, _) -> print_endline "not handled"
  | Constrexpr.CLetIn (_, _, _, _) -> print_endline "not handled"
  | Constrexpr.CAppExpl (_, _) -> print_endline "not handled"
  | Constrexpr.CApp (f, args) ->
      print_endline "applying a function";
      print_info_constr_expr f;
      List.iter (fun (expr, _) -> print_info_constr_expr expr) args
  | Constrexpr.CProj (_, _, _, _) -> print_endline "not handled"
  | Constrexpr.CRecord _ -> print_endline "not handled"
  | Constrexpr.CCases (_, _, _, _) -> print_endline "not handled"
  | Constrexpr.CLetTuple (_, _, _, _) -> print_endline "not handled"
  | Constrexpr.CIf (_, _, _, _) -> print_endline "not handled"
  | Constrexpr.CHole _ -> print_endline "not handled"
  | Constrexpr.CGenarg _ -> print_endline "not handled"
  | Constrexpr.CGenargGlob _ -> print_endline "not handled"
  | Constrexpr.CPatVar _ -> print_endline "not handled"
  | Constrexpr.CEvar (_, _) -> print_endline "E var"
  | Constrexpr.CSort _ -> print_endline "not handled"
  | Constrexpr.CCast (_, _, _) -> print_endline "casting into"
  | Constrexpr.CNotation (scope, (notation_entry, notation_key), substitution)
    ->
      let expr_l1, expr_ll, _, _ = substitution in
      print_endline "that a notation";
      print_endline notation_key;
      List.iter
        (fun (x : Constrexpr.constr_expr) -> print_info_constr_expr x)
        expr_l1
  | Constrexpr.CGeneralization (_, _) -> print_endline "not handled"
  | Constrexpr.CPrim prim_token -> print_prim_token prim_token
  | Constrexpr.CDelimiters (_, _, _) -> print_endline "not handled"
  | Constrexpr.CArray (_, _, _, _) -> print_endline "not handled"

let is_raw_assert (tac : Ltac_plugin.Tacexpr.raw_tactic_expr) : bool =
  match tac.CAst.v with
  | Ltac_plugin.Tacexpr.TacAtom atom -> (
      match atom with
      | Ltac_plugin__Tacexpr.TacAssert (_, _, _, _, _) -> true
      | _ -> false)
  | _ -> false

let get_assert_constr_expr (tac : Ltac_plugin.Tacexpr.raw_tactic_expr) :
    Constrexpr.constr_expr option =
  match tac.CAst.v with
  | Ltac_plugin.Tacexpr.TacAtom atom -> (
      match atom with
      | Ltac_plugin.Tacexpr.TacAssert (_, _, _, _, e) -> Some e
      | _ -> None)
  | _ -> None

let rec replace_func (old_fun_name : string)
    (new_func_name : Constrexpr.constr_expr) (term : Constrexpr.constr_expr) :
    Constrexpr.constr_expr * bool =
  match term.v with
  | Constrexpr.CRef (qualid, instance_expr) -> (term, false)
  | Constrexpr.CFix (_, _) -> (term, false)
  | Constrexpr.CCoFix (_, _) -> (term, false)
  | Constrexpr.CProdN (binders, expr) ->
      let new_expr, had_subst = replace_func old_fun_name new_func_name expr in
      (CAst.make (Constrexpr.CProdN (binders, new_expr)), had_subst)
  | Constrexpr.CLambdaN (binders, expr) ->
      replace_func old_fun_name new_func_name expr
  | Constrexpr.CLetIn (name, expr, expr_opt, expr_bis) ->
      ( CAst.make
          (Constrexpr.CLetIn
             ( name,
               fst (replace_func old_fun_name new_func_name expr),
               Option.map fst
                 (Option.map (replace_func old_fun_name new_func_name) expr_opt),
               fst (replace_func old_fun_name new_func_name expr_bis) )),
        false )
  | Constrexpr.CAppExpl (_, _) -> (term, false)
  | Constrexpr.CApp (f, args) -> (
      match f.v with
      | Constrexpr.CRef (qualid, _) ->
          if Libnames.string_of_qualid qualid = old_fun_name then
            (CAst.make (Constrexpr.CApp (new_func_name, args)), true)
          else (term, false)
      | _ -> (term, false))
  | Constrexpr.CProj (_, _, _, _) -> (term, false)
  | Constrexpr.CRecord list -> (term, false)
  | Constrexpr.CCases (_, _, _, _) -> (term, false)
  | Constrexpr.CLetTuple (_, _, _, _) -> (term, false)
  | Constrexpr.CIf (_, _, _, _) -> (term, false)
  | Constrexpr.CHole _ -> (term, false)
  | Constrexpr.CGenarg _ -> (term, false)
  | Constrexpr.CGenargGlob _ -> (term, false)
  | Constrexpr.CPatVar _ -> (term, false)
  | Constrexpr.CEvar (existential_name, named_exprs) -> (term, false)
  | Constrexpr.CSort _ -> (term, false)
  | Constrexpr.CCast (from, cast_kind, to_) -> (term, false)
  | Constrexpr.CNotation
      (opt_scope, (notation_entry, notation_key), substitution) ->
      let expr_l1, expr_ll, kinded_cases_pattern_expr_l, local_binders_ll =
        substitution
      in
      let mapped_expr_l_pairs =
        List.map (fun x -> replace_func old_fun_name new_func_name x) expr_l1
      in
      let mapped_expr_l, substs = List.split mapped_expr_l_pairs in
      let had_subst = List.fold_left ( || ) false substs in

      let new_subst =
        (mapped_expr_l, expr_ll, kinded_cases_pattern_expr_l, local_binders_ll)
      in

      ( CAst.make
          (Constrexpr.CNotation
             (opt_scope, (notation_entry, notation_key), new_subst)),
        had_subst )
  | Constrexpr.CGeneralization (bindind_kind, expr) -> (term, false)
  | Constrexpr.CPrim _ -> (term, false)
  | Constrexpr.CDelimiters (depth, identifier, expr) -> (term, false)
  | Constrexpr.CArray (_, _, _, _) -> (term, false)

(* this should be a theorem syntax node  *)
let replace_bet_by_betl (x : proof) : transformation_step option =
  let x_start = x.proposition.range.start in
  let components = Option.get (Proof.get_theorem_components x) in
  let expr = components.expr in
  let qualid = Libnames.qualid_of_string "BetL" in
  let g_long_func = CAst.make (Constrexpr.CRef (qualid, None)) in
  let new_expr, did_replace = replace_func "Bet" g_long_func expr in
  if did_replace then (
    let new_components = { components with expr = new_expr } in
    let new_node =
      Proof.syntax_node_from_theorem_components new_components x_start
    in
    print_endline new_node.repr;
    Some (Replace (x.proposition.id, new_node)))
  else None

let experiment_theorem ~io ~token:_ ~(doc : Doc.t) =
  let uri = doc.uri in
  let uri_str = Lang.LUri.File.to_string_uri uri in

  let parsed_document = Coq_document.parse_document doc in

  let proofs = Result.get_ok (Coq_document.get_proofs parsed_document) in

  let proof_sexps =
    List.filter_map Theorem_query.get_proof_proposition_sexp proofs
  in

  let exists_query =
    Q_anywhere
      (Q_list_prefix
         [
           Q_atom "CNotation";
           Q_empty;
           Q_list_exact [ Q_atom "InConstrEntry"; Q_atom "exists _ .. _ , _" ];
         ])
  in

  (* List.iter *)
  (*   (fun x -> *)
  (*     if Theorem_query.matches exists_query x then *)
  (*       print_endline (Sexplib.Sexp.to_string_hum (remove_loc x))) *)
  (*   proof_sexps; *)
  let replace_bet_by_betl_steps =
    List.filter_map (fun proof -> replace_bet_by_betl proof) proofs
  in

  let new_doc =
    Coq_document.apply_transformations_steps replace_bet_by_betl_steps
      parsed_document
  in

  match new_doc with
  | Ok res ->
      let filename = Filename.remove_extension uri_str ^ "_bis.v" in
      print_endline ("All transformations applied, writing to file" ^ filename);
      List.iter
        (fun x -> print_endline (Lang.Range.to_string x.range))
        res.elements;
      let out = open_out filename in
      output_string out (Coq_document.dump_to_string res)
  | Error err ->
      print_endline err;

      ()

let main () = Theory.Register.Completed.add experiment_theorem
let () = main ()
