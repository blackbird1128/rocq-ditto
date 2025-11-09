open Fleche
open Ditto
open Ditto.Proof
open Ditto.Diagnostic_utils
open Ditto.Syntax_node
open Vernacexpr
open Theorem_query
open Result

let wrap_to_treeify doc x = Result.get_ok (Runner.treeify_proof doc x)

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

let is_raw_assert (tac : Ltac_plugin.Tacexpr.raw_tactic_expr) : bool =
  match tac.CAst.v with
  | Ltac_plugin.Tacexpr.TacAtom atom -> (
      match atom with
      | Ltac_plugin.Tacexpr.TacAssert (_, _, _, _, _) -> true
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

let replace_func_map (old_fun_name : string) (new_fun_name : string)
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

let replace_bet_by_betl_in_proof (x : proof) : transformation_step option =
  let x_start = x.proposition.range.start in
  let components = Option.get (Proof.get_theorem_components x) in

  let expr = components.expr in

  let replace_by_betl_map = replace_func_map "Bet" "BetL" in
  let new_expr, did_replace =
    Expr_substitution.constr_expr_map replace_by_betl_map expr
  in
  if did_replace then (
    print_endline "in here";
    let new_components = { components with expr = new_expr } in
    let new_node =
      Proof.syntax_node_from_theorem_components new_components x_start
    in

    Some (Replace (x.proposition.id, new_node)))
  else None

let replace_or_by_constructive_or (x : proof) : transformation_step option =
  let x_start = x.proposition.range.start in
  let components = Option.get (Proof.get_theorem_components x) in
  let expr = components.expr in

  let new_expr, did_replace =
    Expr_substitution.constr_expr_map replace_or_by_constructive_or_map expr
  in
  if did_replace then
    let new_components = { components with expr = new_expr } in
    let new_node =
      Proof.syntax_node_from_theorem_components new_components x_start
    in

    Some (Replace (x.proposition.id, new_node))
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
      match replace_if_contains previous_tac new_tac (repr node) with
      | Some rep ->
          let new_node =
            Result.get_ok
              (Syntax_node.syntax_node_of_string rep node.range.start)
          in
          Some (Replace (node.id, new_node))
      | None -> None)
    x.proof_steps

let replace_context (x : Syntax_node.t) : transformation_step option =
  if Syntax_node.is_syntax_node_context x then
    let new_context_str : string =
      "Context {Pred : predicates}\n\
      \        {ITn : independent_Tarski_neutral_dimensionless Pred}\n\
      \        {ES : Eq_stability Pred ITn}\n\
      \        {Dim : dimension}\n\
      \        {ITnD : @independent_Tarski_nD Pred ITn (incr (incr Dim))}."
    in
    let new_context_node =
      Syntax_node.syntax_node_of_string new_context_str x.range.start
      |> Result.get_ok
    in
    Some (Replace (x.id, new_context_node))
  else None

let replace_require (x : Syntax_node.t) : transformation_step option =
  let split_prefix prefix s =
    let plen = String.length prefix in
    if String.length s >= plen && String.sub s 0 plen = prefix then
      Some (prefix, String.sub s plen (String.length s - plen))
    else None
  in
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).v.expr with
      | VernacSynterp synterp_expr -> (
          match synterp_expr with
          | VernacRequire
              (option_libname, export_with_cats_opt, libnames_import_list) -> (
              match List.nth_opt libnames_import_list 0 with
              | Some (qualid, import_filter) ->
                  let qualid_str = Libnames.string_of_qualid qualid in
                  if
                    String.starts_with ~prefix:"GeoCoq.Main.Tarski_dev."
                      qualid_str
                  then
                    let _, postfix =
                      Option.get
                        (split_prefix "GeoCoq.Main.Tarski_dev." qualid_str)
                    in
                    let new_qualid_str = "GeoCoq.Constructive." ^ postfix in
                    let new_qualid = Libnames.qualid_of_string new_qualid_str in
                    let new_head_tuple = (new_qualid, import_filter) in
                    let new_libnames_import_list =
                      new_head_tuple :: List_utils.drop 1 libnames_import_list
                    in
                    let new_expr =
                      VernacSynterp
                        (VernacRequire
                           ( option_libname,
                             export_with_cats_opt,
                             new_libnames_import_list ))
                    in
                    let new_vernac_control =
                      CAst.make { control = []; attrs = []; expr = new_expr }
                    in

                    let new_coq_node =
                      Syntax_node.syntax_node_of_coq_ast
                        (Coq.Ast.of_coq new_vernac_control)
                        x.range.start
                    in
                    Some (Replace (x.id, new_coq_node))
                  else None
              | None -> None)
          | _ -> None)
      | VernacSynPure _ -> None)
  | None -> None

let admit_exists_proof_in_doc (doc : Rocq_document.t) :
    (Rocq_document.t, Error.t) result =
  let proofs = Result.get_ok (Rocq_document.get_proofs doc) in

  let exists_query =
    Q_anywhere
      (Q_list_prefix
         [
           Q_atom "CNotation";
           Q_empty;
           Q_list_exact [ Q_atom "InConstrEntry"; Q_atom "exists _ .. _ , _" ];
         ])
  in

  let proof_sexps_pairs =
    List.filter_map
      (fun proof ->
        match Theorem_query.get_proof_proposition_sexp proof with
        | Some sexp -> Some (proof, sexp)
        | None -> None)
      proofs
  in

  List.fold_left
    (fun doc_acc (proof, proof_sexps) ->
      match doc_acc with
      | Ok doc_acc ->
          if Theorem_query.matches exists_query proof_sexps then
            let steps =
              Result.get_ok
                (Transformations.admit_and_comment_proof_steps doc_acc proof)
            in
            Rocq_document.apply_transformations_steps steps doc_acc
          else Ok doc_acc
      | Error err -> Error err)
    (Ok doc) proof_sexps_pairs

let replace_bet_by_betl_in_doc (doc : Rocq_document.t) :
    (Rocq_document.t, Error.t) result =
  let proofs = Result.get_ok (Rocq_document.get_proofs doc) in

  let replace_bet_by_betl_steps =
    List.filter_map (fun proof -> replace_bet_by_betl_in_proof proof) proofs
  in
  print_endline "entering apply transformation steps in replace bet by betL";

  let r =
    Rocq_document.apply_transformations_steps replace_bet_by_betl_steps doc
  in
  print_endline "exiting apply transformation steps";
  r

let replace_or_by_constructive_or_in_doc (doc : Rocq_document.t) :
    (Rocq_document.t, Error.t) result =
  let proofs = Result.get_ok (Rocq_document.get_proofs doc) in
  let replace_or_by_constructive_or_steps =
    List.filter_map (fun proof -> replace_or_by_constructive_or proof) proofs
  in

  Rocq_document.apply_transformations_steps replace_or_by_constructive_or_steps
    doc

let replace_non_constructive_tactics_in_doc (doc : Rocq_document.t) :
    (Rocq_document.t, Error.t) result =
  let proofs = Result.get_ok (Rocq_document.get_proofs doc) in
  let replace_tactics_steps =
    List.concat_map
      (fun proof ->
        List.concat
          [
            replace_tactic_by_other "left" "stab_left" proof;
            replace_tactic_by_other "right" "stab_right" proof;
            replace_tactic_by_other "segment_construction"
              "apply by segment_construction" proof;
            replace_tactic_by_other "inner_pasch" "apply by_inner_pasch" proof;
          ])
      proofs
  in

  Rocq_document.apply_transformations_steps replace_tactics_steps doc

let replace_context_in_doc (doc : Rocq_document.t) :
    (Rocq_document.t, Error.t) result =
  let context_transform_steps = List.filter_map replace_context doc.elements in
  Rocq_document.apply_transformations_steps context_transform_steps doc

let replace_requires_in_doc (doc : Rocq_document.t) :
    (Rocq_document.t, Error.t) result =
  let require_transform_steps = List.filter_map replace_require doc.elements in

  Rocq_document.apply_transformations_steps require_transform_steps doc

let experiment_theorem ~io:_ ~token:_ ~(doc : Doc.t) =
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
      let ( let* ) = Result.bind in

      let parsed_document = Rocq_document.parse_document doc in

      let res =
        let* doc_with_exists_proof_admitted =
          admit_exists_proof_in_doc parsed_document
        in

        (* List.iter *)
        (*   (fun x -> *)
        (*     print_endline (x.repr ^ " " ^ Code_range.to_string x.range); *)
        (*     print_endline "") *)
        (*   doc_with_exists_proof_admitted.elements; *)
        (* print_endline "------------------------------------------------------"; *)
        let* doc_with_requires_replaced =
          replace_requires_in_doc doc_with_exists_proof_admitted
        in

        let* doc_with_context_replaced =
          replace_context_in_doc doc_with_requires_replaced
        in

        (* let* string_dump = *)
        (*   Rocq_document.dump_to_string doc_with_context_replaced *)
        (* in *)

        (* print_endline string_dump; *)

        (* print_endline "entering replace bet with betL"; *)

        (* let* doc_with_bet_replaced_by_betl = *)
        (*   replace_bet_by_betl_in_doc doc_with_context_replaced *)
        (* in *)

        (* print_endline "ending replacing bet with betL"; *)
        (* let* doc_with_or_replaced_by_constructive_or = *)
        (*   replace_or_by_constructive_or_in_doc doc_with_bet_replaced_by_betl *)
        (* in *)
        Ok doc_with_context_replaced
      in

      match res with
      | Ok res ->
          let filename =
            "../private-geocoq/theories/Constructive/"
            ^ (Filename.basename uri_str |> Filename.remove_extension)
            ^ "_bis.v"
          in
          print_endline
            ("All transformations applied, writing to file" ^ filename);
          let out = open_out filename in
          Result.fold ~ok:(output_string out)
            ~error:(fun e -> print_endline (Error.to_string_hum e))
            (Rocq_document.dump_to_string res)
      | Error err -> print_endline (Error.to_string_hum err))

let main () = Theory.Register.Completed.add experiment_theorem
let () = main ()
