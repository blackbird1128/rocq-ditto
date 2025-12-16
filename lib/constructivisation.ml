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

let replace_taccall_tacarg_in_tacexpr (old_tac_call_name : string)
    (new_tac_call_name : string) (tacexpr : Ltac_plugin.Tacexpr.raw_tactic_expr)
    : Ltac_plugin.Tacexpr.raw_tactic_expr =
  let open Ltac_plugin.Tacexpr in
  match tacexpr.v with
  | TacArg gen_tac_arg -> (
      match gen_tac_arg with
      | TacCall call_arg ->
          let old_call_qualid, old_call_args = call_arg.v in
          let old_call_qualid_str = Libnames.string_of_qualid old_call_qualid in
          let new_tac_call_name_qualid =
            Libnames.qualid_of_string new_tac_call_name
          in
          let new_tac_call =
            CAst.make (new_tac_call_name_qualid, old_call_args)
          in
          if old_call_qualid_str = old_tac_call_name then
            TacArg (TacCall new_tac_call) |> CAst.make
          else tacexpr
      | _ -> tacexpr)
  | _ -> tacexpr

let replace_taccall_tacarg_in_node (old_tac_call_name : string)
    (new_tac_call_name : string) (node : Syntax_node.t) :
    transformation_step option =
  let+ raw_tac_expr = Syntax_node.get_node_raw_tactic_expr node in
  let f =
    replace_taccall_tacarg_in_tacexpr old_tac_call_name new_tac_call_name
  in
  let raw_expr_mapped, did_replace = Tacexpr_map.tacexpr_map f raw_tac_expr in
  if did_replace then
    let selector = Syntax_node.get_node_goal_selector_opt node in
    let+ new_node =
      Syntax_node.raw_tactic_expr_to_syntax_node raw_expr_mapped ?selector
        ~use_default:false node.range.start
      |> Result.to_option
    in
    Some (Replace (node.id, new_node))
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
                  let replace_map =
                    replace_fun_name_in_constrexpr old_fun_name new_fun_name
                  in
                  let new_expr, did_replace =
                    Expr_substitution.constr_expr_map replace_map expr1
                  in
                  if did_replace then
                    let new_define_body =
                      DefineBody (binders, raw_red_expr_opt, new_expr, opt_expr)
                    in
                    let new_vernacexpr =
                      VernacSynPure
                        (VernacDefinition
                           ( (discharge, definition_object_kind),
                             name_decl,
                             new_define_body ))
                    in
                    let new_vernac_control =
                      Syntax_node.mk_vernac_control new_vernacexpr
                    in
                    let new_node =
                      Syntax_node.syntax_node_of_coq_ast
                        (Coq.Ast.of_coq new_vernac_control)
                        x.range.start
                    in
                    Some (Replace (x.id, new_node))
                  else None)
          | _ -> None))
  | None -> None

let replace_notation_in_definition (old_notation : string)
    (new_notation : string) (x : Syntax_node.t) : transformation_step option =
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
                  let replace_map =
                    replace_notation_in_constrexpr old_notation new_notation
                  in

                  let new_expr, did_replace =
                    Expr_substitution.constr_expr_map replace_map expr1
                  in

                  if did_replace then
                    let new_define_body =
                      DefineBody (binders, raw_red_expr_opt, new_expr, opt_expr)
                    in
                    let new_vernacexpr =
                      VernacSynPure
                        (VernacDefinition
                           ( (discharge, definition_object_kind),
                             name_decl,
                             new_define_body ))
                    in
                    let new_vernac_control =
                      Syntax_node.mk_vernac_control new_vernacexpr
                    in
                    let new_node =
                      Syntax_node.syntax_node_of_coq_ast
                        (Coq.Ast.of_coq new_vernac_control)
                        x.range.start
                    in
                    Some (Replace (x.id, new_node))
                  else None)
          | _ -> None))
  | None -> None

let add_node_after_require (doc : Rocq_document.t) (node : Syntax_node.t) :
    transformation_step option =
  let+ last_require =
    List.find_opt Syntax_node.is_syntax_node_require (List.rev doc.elements)
  in
  Some (Attach (node, LineAfter, last_require.id))

type definition_object_kind = [%import: Decls.definition_object_kind]
[@@deriving show]

let fold_constr_expr (f : 'a -> Constrexpr.constr_expr -> 'a) (init : 'a)
    (t : Constrexpr.constr_expr) : Constrexpr.constr_expr =
  Constrexpr_ops.fold_constr_expr_with_binders
    (fun _ a -> a) (* ignore binders *)
    (fun _ acc e -> f acc e)
    () init t

let map_constr_expr (f : Constrexpr.constr_expr -> Constrexpr.constr_expr)
    (t : Constrexpr.constr_expr) : Constrexpr.constr_expr =
  Constrexpr_ops.map_constr_expr_with_binders
    (fun _ a -> a)
    (fun _ (e : Constrexpr.constr_expr) -> f e)
    () t

let is_proof_about_exists (p : Proof.t) : bool =
  let ( let@ ) o f = match o with None -> false | Some x -> f x in
  let@ components = Proof.get_theorem_components p in

  Constrexpr_fold.exists
    (fun expr ->
      match expr.v with
      | Constrexpr.CNotation
          (opt_scope, (notation_entry, notation_key), notation_substitution) ->
          notation_key = "exists _ .. _ , _"
      | _ -> false)
    components.expr

let rec update_replaces (l : transformation_step list) =
  match l with
  | [] -> []
  | x :: tl -> (
      match x with
      | Replace (id_curr, new_node_curr) ->
          let new_tl =
            List.map
              (fun el_tl ->
                match el_tl with
                | Replace (id_el, new_node_el) ->
                    if Uuidm.equal id_el id_curr then
                      Replace (new_node_curr.id, new_node_el)
                    else Replace (id_el, new_node_el)
                | Attach (new_node_el, attach_position, id_el) ->
                    if Uuidm.equal id_el id_curr then
                      Attach (new_node_el, attach_position, new_node_curr.id)
                    else Replace (id_el, new_node_el)
                | Add _ | Remove _ -> el_tl)
              tl
          in
          x :: update_replaces new_tl
      | Add _ | Remove _ | Attach _ -> x :: update_replaces tl)

(* remove all the steps referring to a removed node *)
let rec update_removes (l : transformation_step list) =
  match l with
  | [] -> []
  | x :: tl -> (
      match x with
      | Remove id_curr ->
          let new_tl =
            List.filter_map
              (fun el_tl ->
                match el_tl with
                | Replace (id_el, _) | Remove id_el ->
                    if Uuidm.equal id_el id_curr then None else Some el_tl
                | Add _ | Attach _ -> Some el_tl)
              tl
          in
          x :: update_removes new_tl
      | Add _ | Replace _ | Attach _ -> x :: update_removes tl)

let constructivize_doc (doc : Rocq_document.t) :
    (transformation_step list, Error.t) result =
  let token = Coq.Limits.Token.create () in
  let* proofs = Rocq_document.get_proofs doc in
  let dummy_start : Code_point.t = { line = 0; character = 0 } in

  let* require_stable_node =
    Syntax_node.syntax_node_of_string
      "Require Import GeoCoq.Constructive.Stable." dummy_start
  in
  let _ =
    Runner.get_state_after doc.initial_state token [ require_stable_node ]
    (* Require Geocoq.Constructive.Stable in the context for syntax_node_of_string ? this is a bit weird but for now, we need to inform Rocq of other export like this, this is not pure at all :[ *)
  in

  (* stage 0 *)
  let* definitions_file_specific_steps =
    if Filename.basename doc.filename = "Definitions.v" then
      let first_require =
        List.find Syntax_node.is_syntax_node_require doc.elements
      in
      let* new_first_require =
        Syntax_node.syntax_node_of_string
          "Require Export \
           GeoCoq.Algebraic.Counter_models.nD.independent_version."
          first_require.range.start
      in
      let* second_require =
        Syntax_node.syntax_node_of_string
          "Require Export GeoCoq.Constructive.Stable." dummy_start
      in
      (* the node is attached so we dont care where it start *)

      let* third_require =
        Syntax_node.syntax_node_of_string
          "Require Import \
           GeoCoq.Algebraic.Counter_models.nD.stability_properties."
          dummy_start
      in

      let* betl_definition =
        Syntax_node.syntax_node_of_string
          "Definition BetL {Pred : predicates}\n\
          \                {ITn : independent_Tarski_neutral_dimensionless Pred}\n\
          \                {ES : Eq_stability Pred ITn}\n\
          \                {Dim : dimension}\n\
          \                {ITnD : @independent_Tarski_nD Pred ITn (incr (incr \
           Dim))}\n\
          \                A B C := A = B \\_/ B = C \\_/ BetS A B C."
          dummy_start
      in

      Ok
        [
          Replace (first_require.id, new_first_require);
          Attach (second_require, LineAfter, new_first_require.id);
          Attach (third_require, LineAfter, second_require.id);
          Attach (betl_definition, LineAfter, third_require.id);
        ]
    else Ok []
  in

  let replace_require_steps = List.filter_map replace_require doc.elements in

  let replace_context_steps = List.filter_map replace_context doc.elements in

  (* let* admit_proof_steps = *)
  (*   List.fold_left *)
  (*     (fun res_acc proof -> *)
  (*       match res_acc with *)
  (*       | Ok res_acc -> *)
  (*           let* steps = *)
  (*             Transformations.admit_and_comment_proof_steps doc proof *)
  (*           in *)
  (*           Ok (steps @ res_acc) *)
  (*       | Error err -> Error err) *)
  (*     (Ok []) proofs *)
  (* in *)
  let definitions =
    List.filter Syntax_node.is_syntax_node_definition doc.elements
  in

  let replace_or_by_constructive_or_in_proofs_steps =
    List.filter_map
      (replace_notation_in_proof_proposition "_ \\/ _" "_ \\_/ _")
      proofs
  in

  let replace_or_by_constructive_or_in_definitions_steps =
    List.filter_map
      (replace_notation_in_definition "_ \\/ _" "_ \\_/ _")
      definitions
  in

  let steps_stage_zero =
    replace_require_steps @ replace_context_steps
    @ replace_or_by_constructive_or_in_proofs_steps
    @ replace_or_by_constructive_or_in_definitions_steps
    @ definitions_file_specific_steps
  in
  (***** end of stage 1 **************)

  let* stage_one_doc =
    Rocq_document.apply_transformations_steps steps_stage_zero doc
  in

  let* proofs_stage_one = Rocq_document.get_proofs stage_one_doc in

  let proofs_with_exists = List.filter is_proof_about_exists proofs_stage_one in
  List.iter
    (fun x -> Logs.debug (fun m -> m "%s" (Syntax_node.repr x.proposition)))
    proofs_with_exists;

  let* admit_exists_proofs_steps =
    List.fold_left
      (fun res_acc proof ->
        match res_acc with
        | Ok res_acc ->
            let* steps =
              Transformations.admit_and_comment_proof_steps doc proof
            in
            Ok (steps @ res_acc)
        | Error err -> Error err)
      (Ok []) proofs_with_exists
  in

  let steps_stage_one = admit_exists_proofs_steps in

  let* stage_two_doc =
    Rocq_document.apply_transformations_steps steps_stage_one stage_one_doc
  in

  let* proofs_stage_two = Rocq_document.get_proofs stage_two_doc in

  let definitions_stage_two =
    List.filter Syntax_node.is_syntax_node_definition stage_two_doc.elements
  in

  let replace_bet_by_betl_in_proofs_steps =
    List.filter_map (replace_fun_name_in_proof "Bet" "BetL") proofs_stage_two
  in

  let replace_bet_by_betl_in_definitions_steps =
    List.filter_map
      (replace_fun_name_in_definition "Bet" "BetL")
      definitions_stage_two
  in

  let replace_left_by_stab_left =
    List.filter_map
      (replace_taccall_tacarg_in_node "left" "stab_left")
      stage_two_doc.elements
  in

  let steps_stage_two =
    replace_bet_by_betl_in_proofs_steps
    @ replace_bet_by_betl_in_definitions_steps @ replace_left_by_stab_left
  in

  let* stage_three_doc =
    Rocq_document.apply_transformations_steps steps_stage_two stage_two_doc
  in

  let replace_right_by_stab_right =
    List.filter_map
      (replace_taccall_tacarg_in_node "right" "stab_right")
      stage_three_doc.elements
  in

  let steps_stage_three = replace_right_by_stab_right in

  Ok
    (update_replaces steps_stage_zero
    @ steps_stage_one @ steps_stage_two @ steps_stage_three)
