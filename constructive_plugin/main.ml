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
  let _ =
    match x.loc with
    | Some loc -> Pp.pp_with Format.std_formatter (Loc.pr loc)
    | None -> ()
  in
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

let rec replace_func_map (old_fun_name : string) (new_fun_name : string)
    (term : Constrexpr.constr_expr) : Constrexpr.constr_expr =
  match term.v with
  | Constrexpr.CApp (f, args) -> (
      match f.v with
      | Constrexpr.CRef (qualid, _) ->
          if Libnames.string_of_qualid qualid = old_fun_name then
            let new_fun_qualid = Libnames.qualid_of_string new_fun_name in
            let new_fun = CAst.make (Constrexpr.CRef (new_fun_qualid, None)) in
            CAst.make (Constrexpr.CApp (new_fun, args))
          else term
      | _ -> term)
  | _ -> term

let replace_or_by_constructive_or_map (term : Constrexpr.constr_expr) :
    Constrexpr.constr_expr =
  match term.v with
  | CNotation (scope, (entry, key), (l1, ll, pat, binders)) ->
      if key = "_ \\/ _" then
        CAst.make
          (Constrexpr.CNotation
             (scope, (entry, "_ \\_/ _"), (l1, ll, pat, binders)))
      else term
  | _ -> term

let replace_bet_by_betl (x : proof) : transformation_step option =
  let x_start = x.proposition.range.start in
  let components = Option.get (Proof.get_theorem_components x) in
  let expr = components.expr in

  let replace_by_betl_map = replace_func_map "Bet" "BetL" in
  let new_expr, did_replace =
    Expr_substitution.constr_expr_map replace_by_betl_map expr
  in
  if did_replace then
    let new_components = { components with expr = new_expr } in
    let new_node =
      Proof.syntax_node_from_theorem_components new_components x_start
    in

    Some (Replace (x.proposition.id, new_node))
  else None

let replace_or_by_constructive_or (x : proof) : transformation_step option =
  let x_start = x.proposition.range.start in
  let components = Option.get (Proof.get_theorem_components x) in
  let expr = components.expr in

  let new_expr, did_replace =
    Expr_substitution.constr_expr_map replace_or_by_constructive_or_map expr
  in
  if did_replace then (
    print_endline "replacement yeah";
    let new_components = { components with expr = new_expr } in
    let new_node =
      Proof.syntax_node_from_theorem_components new_components x_start
    in

    Some (Replace (x.proposition.id, new_node)))
  else None

let replace_tactic_by_other (previous_tac : string) (new_tac : string)
    (x : proof) : transformation_step list =
  let replace_if_contains target replacement s =
    let re = Re.compile (Re.str target) in
    if Re.execp re s then
      Some (Re.replace_string ~all:true re ~by:replacement s)
    else None
  in

  List.filter_map
    (fun node ->
      match replace_if_contains previous_tac new_tac node.repr with
      | Some rep ->
          let new_node =
            Result.get_ok
              (Syntax_node.syntax_node_of_string rep node.range.start)
          in
          Some (Replace (node.id, new_node))
      | None -> None)
    x.proof_steps

let coq_init ~debug =
  let load_module = Dynlink.loadfile in
  let load_plugin = Coq.Loader.plugin_handler None in
  let vm, warnings = (true, None) in
  Coq.Init.(coq_init { debug; load_module; load_plugin; vm; warnings })

let by_load ~io ~token:tok ~(doc : Doc.t) =
  let uri = doc.uri in
  let uri_str = Lang.LUri.File.to_string_uri uri in

  let env = doc.env in
  let diags = List.concat_map (fun (x : Doc.Node.t) -> x.diags) doc.nodes in
  let errors = List.filter Lang.Diagnostic.is_error diags in

  match doc.completed with
  | Doc.Completion.Stopped range_stop ->
      prerr_endline ("parsing stopped at " ^ Lang.Range.to_string range_stop);
      print_diagnostics errors
  | Doc.Completion.Failed range_failed ->
      prerr_endline ("parsing failed at " ^ Lang.Range.to_string range_failed);
      print_diagnostics errors
  | Doc.Completion.Yes _ -> (
      let parsed__first_document = Coq_document.parse_document doc in

      let other_doc_path = "./test/fixtures/ex_id_assign2.v" in
      let other_doc_uri = Lang.LUri.of_string other_doc_path in
      let other_doc_file =
        Result.get_ok (Lang.LUri.File.of_uri other_doc_uri)
      in

      let other_doc_raw_content = File_utils.read_whole_file other_doc_path in
      print_endline other_doc_raw_content;
      let other_doc =
        Fleche.Doc.create ~token:tok ~env ~uri ~version:1
          ~raw:other_doc_raw_content
      in
      match other_doc.completed with
      | Doc.Completion.Stopped range_stop ->
          let diags =
            List.concat_map (fun (x : Doc.Node.t) -> x.diags) other_doc.nodes
          in
          let errors = List.filter Lang.Diagnostic.is_error diags in
          prerr_endline
            ("parsing of the second file stopped at "
            ^ Lang.Range.to_string range_stop);
          print_diagnostics diags
      | Doc.Completion.Failed range_failed ->
          prerr_endline
            ("parsing failed at " ^ Lang.Range.to_string range_failed);
          print_diagnostics errors
      | Doc.Completion.Yes _ ->
          print_endline "the second doc was parsed succesfully";

          ())

let experiment_theorem ~io ~token:_ ~(doc : Doc.t) =
  let uri = doc.uri in
  let uri_str = Lang.LUri.File.to_string_uri uri in

  let diags = List.concat_map (fun (x : Doc.Node.t) -> x.diags) doc.nodes in
  let errors = List.filter Lang.Diagnostic.is_error diags in

  match doc.completed with
  | Doc.Completion.Stopped range_stop ->
      prerr_endline ("parsing stopped at " ^ Lang.Range.to_string range_stop);
      print_diagnostics errors
  | Doc.Completion.Failed range_failed ->
      prerr_endline ("parsing failed at " ^ Lang.Range.to_string range_failed);
      print_diagnostics errors
  | Doc.Completion.Yes _ -> (
      let parsed_document = Coq_document.parse_document doc in

      let proofs = Result.get_ok (Coq_document.get_proofs parsed_document) in

      let exists_query =
        Q_anywhere
          (Q_list_prefix
             [
               Q_atom "CNotation";
               Q_empty;
               Q_list_exact
                 [ Q_atom "InConstrEntry"; Q_atom "exists _ .. _ , _" ];
             ])
      in

      let replace_bet_by_betl_steps =
        List.filter_map (fun proof -> replace_bet_by_betl proof) proofs
      in

      let new_doc =
        Result.get_ok
          (Coq_document.apply_transformations_steps replace_bet_by_betl_steps
             parsed_document)
      in

      let proofs = Result.get_ok (Coq_document.get_proofs parsed_document) in

      let replace_or_by_constructive_or_steps =
        List.filter_map
          (fun proof -> replace_or_by_constructive_or proof)
          proofs
      in

      let new_doc =
        Result.get_ok
          (Coq_document.apply_transformations_steps
             replace_or_by_constructive_or_steps new_doc)
      in

      let proofs = Result.get_ok (Coq_document.get_proofs new_doc) in
      (* replacement can be made into any order *)
      let proof_sexps_pairs =
        List.filter_map
          (fun proof ->
            match Theorem_query.get_proof_proposition_sexp proof with
            | Some sexp -> Some (proof, sexp)
            | None -> None)
          proofs
      in

      let new_doc =
        Result.get_ok
          (List.fold_left
             (fun doc_acc (proof, proof_sexps) ->
               match doc_acc with
               | Ok doc_acc ->
                   if Theorem_query.matches exists_query proof_sexps then
                     let steps =
                       Result.get_ok (Transformations.admit_proof doc_acc proof)
                     in
                     Coq_document.apply_transformations_steps steps doc_acc
                   else Ok doc_acc
               | Error err -> Error err)
             (Ok new_doc) proof_sexps_pairs)
      in

      let proofs = Result.get_ok (Coq_document.get_proofs new_doc) in

      let replace_tactics_steps =
        List.concat_map
          (fun proof ->
            List.concat
              [
                replace_tactic_by_other "left" "stab_left" proof;
                replace_tactic_by_other "right" "stab_right" proof;
                replace_tactic_by_other "segment_construction"
                  "apply by segment_construction" proof;
                replace_tactic_by_other "inner_pasch" "apply by_inner_pasch"
                  proof;
              ])
          proofs
      in

      let new_doc =
        Coq_document.apply_transformations_steps replace_tactics_steps new_doc
      in

      match new_doc with
      | Ok res ->
          let filename = Filename.remove_extension uri_str ^ "_bis.v" in
          print_endline
            ("All transformations applied, writing to file" ^ filename);
          (* List.iter *)
          (*   (fun x -> print_endline (Lang.Range.to_string x.range)) *)
          (*   res.elements; *)
          let out = open_out filename in
          output_string out (Coq_document.dump_to_string res)
      | Error err ->
          print_endline err;

          ())

let main () = Theory.Register.Completed.add by_load
let () = main ()
