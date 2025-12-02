open Proof
open Vernacexpr

let ( let* ) = Result.bind
let ( let+ ) = Option.bind

let replace_require (x : Syntax_node.t) : transformation_step option =
  let split_prefix (prefix : string) (s : string) =
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

                    let new_node =
                      Syntax_node.syntax_node_of_coq_ast
                        (Coq.Ast.of_coq new_vernac_control)
                        x.range.start
                    in
                    Some (Replace (x.id, new_node))
                  else None
              | None -> None)
          | _ -> None)
      | VernacSynPure _ -> None)
  | None -> None

let replace_context (x : Syntax_node.t) : transformation_step option =
  if Syntax_node.is_syntax_node_context x then
    let new_context_str : string =
      "Context {Pred : predicates}\n\
      \        {ITn : independent_Tarski_neutral_dimensionless Pred}\n\
      \        {ES : Eq_stability Pred ITn}\n\
      \        {Dim : dimension}\n\
      \        {ITnD : @independent_Tarski_nD Pred ITn (incr (incr Dim))}."
    in
    let+ new_context_node =
      Syntax_node.syntax_node_of_string new_context_str x.range.start
      |> Result.to_option
    in
    Some (Replace (x.id, new_context_node))
  else None

let replace_notation_in_constrexpr (old_notation : string)
    (new_notation : string) (term : Constrexpr.constr_expr) :
    Constrexpr.constr_expr =
  match term.v with
  | CNotation (scope, (entry, key), (l1, ll, pat, binders)) ->
      if key = old_notation then
        CAst.make
          (Constrexpr.CNotation
             (scope, (entry, new_notation), (l1, ll, pat, binders)))
      else term
  | _ -> term

let replace_notation_in_proof_proposition (old_notation : string)
    (new_notation : string) (x : Proof.t) : transformation_step option =
  let x_start = x.proposition.range.start in
  let+ components = Proof.get_theorem_components x in

  let new_expr, did_replace =
    Expr_substitution.constr_expr_map
      (replace_notation_in_constrexpr old_notation new_notation)
      components.expr
  in
  if did_replace then
    let new_components = { components with expr = new_expr } in

    let new_node =
      Proof.syntax_node_of_theorem_components new_components x_start
    in

    Some (Replace (x.proposition.id, new_node))
  else None

let replace_fun_name_in_constrexpr (old_fun_name : string)
    (new_fun_name : string) (term : Constrexpr.constr_expr) :
    Constrexpr.constr_expr =
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

let replace_fun_name_in_proof (old_fun_name : string) (new_fun_name : string)
    (x : Proof.t) : transformation_step option =
  let x_start = x.proposition.range.start in
  let+ components = Proof.get_theorem_components x in

  let expr = components.expr in

  let replace_map = replace_fun_name_in_constrexpr old_fun_name new_fun_name in
  let new_expr, did_replace =
    Expr_substitution.constr_expr_map replace_map expr
  in
  if did_replace then
    let new_components = { components with expr = new_expr } in
    let new_node =
      Proof.syntax_node_of_theorem_components new_components x_start
    in

    Some (Replace (x.proposition.id, new_node))
  else None

let constrexpr_to_string (x : Constrexpr.constr_expr) : string =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let pp = Ppconstr.pr_constr_expr env sigma x in
  Pp.string_of_ppcmds pp

let replace_fun_name_in_definition (old_fun_name : string)
    (new_fun_name : string) (x : Syntax_node.t) : transformation_step option =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).CAst.v.expr with
      | VernacSynterp _ -> None
      | VernacSynPure expr -> (
          match expr with
          | Vernacexpr.VernacDefinition
              ( (discharge, definition_object_kind),
                (name_decl : Constrexpr.name_decl),
                expr ) -> (
              match expr with
              | ProveBody _ -> None
              | DefineBody (binders, raw_red_expr_opt, expr1, opt_expr) ->
                  Logs.debug (fun m -> m "DefineBody");
                  Logs.debug (fun m ->
                      m "expr1: %s" (constrexpr_to_string expr1));

                  let replace_map =
                    replace_fun_name_in_constrexpr old_fun_name new_fun_name
                  in
                  let new_expr, did_replace =
                    Expr_substitution.constr_expr_map replace_map expr1
                  in

                  if did_replace then None else None)
          | _ -> None))
  | None -> None

type definition_object_kind = [%import: Decls.definition_object_kind]
[@@deriving show]

let constructivize_doc (doc : Rocq_document.t) :
    (transformation_step list, Error.t) result =
  let* proofs = Rocq_document.get_proofs doc in
  let* admit_proof_steps =
    List.fold_left
      (fun res_acc proof ->
        match res_acc with
        | Ok res_acc ->
            let* steps =
              Transformations.admit_and_comment_proof_steps doc proof
            in
            Ok (steps @ res_acc)
        | Error err -> Error err)
      (Ok []) proofs
  in

  let replace_require_steps = List.filter_map replace_require doc.elements in

  let replace_contex_steps = List.filter_map replace_context doc.elements in

  let replace_or_by_constructive_or_steps =
    List.filter_map
      (replace_notation_in_proof_proposition "_ \\/ _" "_ \\_/ _")
      proofs
  in

  let replace_bet_by_betl_steps =
    List.filter_map (replace_fun_name_in_proof "Bet" "BetL") proofs
  in

  let definitions =
    List.filter Syntax_node.is_syntax_node_definition doc.elements
  in
  List.iter
    (fun (x : Syntax_node.t) ->
      match x.ast with
      | Some ast -> (
          match (Coq.Ast.to_coq ast.v).CAst.v.expr with
          | VernacSynterp _ -> ()
          | VernacSynPure expr -> (
              match expr with
              | Vernacexpr.VernacDefinition
                  ( (discharge, definition_object_kind),
                    (name_decl : Constrexpr.name_decl),
                    expr ) -> (
                  Logs.debug (fun m ->
                      m "definition kind: %s"
                        (show_definition_object_kind definition_object_kind));
                  let lname, univ_decl_expr_opt = name_decl in
                  Logs.debug (fun m ->
                      m "lname: %s"
                        (Pp.string_of_ppcmds (Names.Name.print lname.v)));
                  match expr with
                  | ProveBody (binders, expr) ->
                      Logs.debug (fun m -> m "ProveBody");
                      ()
                  | DefineBody (binders, raw_red_expr_opt, expr1, opt_expr) ->
                      Logs.debug (fun m -> m "DefineBody");
                      Logs.debug (fun m ->
                          m "expr1: %s" (constrexpr_to_string expr1));
                      ())
              | _ -> ()))
      | None -> ())
    definitions;

  Ok
    (replace_require_steps @ replace_contex_steps @ admit_proof_steps
   @ replace_or_by_constructive_or_steps @ replace_bet_by_betl_steps)
