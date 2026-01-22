open Proof
open Vernacexpr

let ( let* ) = Result.bind
let ( let+ ) = Option.bind

let get_new_vars ?(keep : string list = [])
    (old_goals_vars : string list list option)
    (new_goals_vars : string list list option) : string list list option =
  match (old_goals_vars, new_goals_vars) with
  | Some old_goals_vars, Some new_goals_vars ->
      Some
        (List_utils.map2_pad
           ~pad1:(List.nth_opt old_goals_vars 0)
           (fun old_vars new_vars ->
             List.filter
               (fun x -> (not (List.mem x old_vars)) || List.mem x keep)
               new_vars)
           old_goals_vars new_goals_vars)
  | _ -> None

let constrexpr_to_string (x : Constrexpr.constr_expr) : string =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let pp = Ppconstr.pr_constr_expr env sigma x in
  Pp.string_of_ppcmds pp

let rec remove_loc (s : Sexplib.Sexp.t) : Sexplib.Sexp.t option =
  match s with
  | Atom _ as a -> Some a
  | List (Atom "loc" :: _) -> None (* drop the whole (loc ...) *)
  | List xs ->
      let xs' = xs |> List.filter_map remove_loc in
      Some (List xs')

let strip_loc sexp =
  match remove_loc sexp with
  | Some s -> s
  | None -> List [] (* should basically never happen at the top *)

let replace_require (x : Syntax_node.t) :
    (transformation_step list, Error.t) result =
  let split_prefix (prefix : string) (s : string) =
    let plen = String.length prefix in
    if String.length s >= plen && String.sub s 0 plen = prefix then
      Some (prefix, String.sub s plen (String.length s - plen))
    else None
  in
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).v.expr with
      | VernacSynterp
          (VernacRequire
             (option_libname, export_with_cats_opt, libnames_import_list)) -> (
          match List.nth_opt libnames_import_list 0 with
          | Some (qualid, import_filter) -> (
              let qualid_str = Libnames.string_of_qualid qualid in
              match split_prefix "GeoCoq.Main.Tarski_dev" qualid_str with
              | Some (_, postfix) ->
                  let new_qualid_str = "GeoCoq.Constructive" ^ postfix in

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
                    Syntax_node.mk_vernac_control new_expr
                  in

                  let new_node =
                    Syntax_node.syntax_node_of_coq_ast
                      (Coq.Ast.of_coq new_vernac_control)
                      x.range.start
                  in
                  Ok [ Replace (x.id, new_node) ]
              | None -> Ok [])
          | None ->
              Error.format_to_or_error
                "Error getting libnames_import_list in %s" (Syntax_node.repr x))
      | _ -> Ok [])
  | None -> Ok []

let replace_context (x : Syntax_node.t) :
    (transformation_step list, Error.t) result =
  if Syntax_node.is_syntax_node_context x then
    let new_context_str : string =
      "Context {Pred : predicates}\n\
      \        {ITn : independent_Tarski_neutral_dimensionless Pred}\n\
      \        {ES : Eq_stability Pred ITn}\n\
      \        {Dim : dimension}\n\
      \        {ITnD : @independent_Tarski_nD Pred ITn (incr (incr Dim))}."
    in
    let* new_context_node =
      Syntax_node.syntax_node_of_string new_context_str x.range.start
    in

    Ok [ Replace (x.id, new_context_node) ]
  else Ok []

let replace_notation_in_constrexpr (old_notation : string)
    (new_notation : string) (term : Constrexpr.constr_expr) :
    Constrexpr.constr_expr =
  match term.v with
  | CNotation (scope, (entry, key), (l1, ll, pat, binders))
    when key = old_notation ->
      CAst.make
        (Constrexpr.CNotation
           (scope, (entry, new_notation), (l1, ll, pat, binders)))
  | _ -> term

let replace_fun_name_in_constrexpr (old_fun_name : string)
    (new_fun_name : string) (term : Constrexpr.constr_expr) :
    Constrexpr.constr_expr =
  let old_q = Libnames.qualid_of_string old_fun_name in
  let new_q = Libnames.qualid_of_string new_fun_name in

  let matches_ref q =
    (* more robust than string_of_qualid equality *)
    Libnames.qualid_eq q old_q
  in

  match term.v with
  | Constrexpr.CRef (q, instance_expr_opt) when matches_ref q ->
      CAst.make (Constrexpr.CRef (new_q, instance_expr_opt))
  | Constrexpr.CAppExpl ((q, instance_expr_opt), l) when matches_ref q ->
      CAst.make (Constrexpr.CAppExpl ((new_q, instance_expr_opt), l))
  | _ -> term

let map_proof_proposition (f : Constrexpr.constr_expr -> Constrexpr.constr_expr)
    (x : Proof.t) : transformation_step option =
  let x_start = x.proposition.range.start in
  let+ components = Proof.get_theorem_components x in

  let new_expr = Constrexpr_map.constr_expr_map f components.expr in
  if not (Constrexpr_ops.constr_expr_eq components.expr new_expr) then
    let new_components = { components with expr = new_expr } in

    let new_node =
      Proof.syntax_node_of_theorem_components new_components x_start
    in

    Some (Replace (x.proposition.id, new_node))
  else None

let replace_notation_in_proof_proposition (old_notation : string)
    (new_notation : string) (x : Proof.t) : transformation_step option =
  map_proof_proposition
    (replace_notation_in_constrexpr old_notation new_notation)
    x

let replace_fun_name_in_proof_proposition (old_fun_name : string)
    (new_fun_name : string) (x : Proof.t) : transformation_step option =
  map_proof_proposition
    (replace_fun_name_in_constrexpr old_fun_name new_fun_name)
    x

let is_syntax_node_prolong (x : Syntax_node.t) : bool =
  let ( let@ ) opt f = match opt with Some x -> f x | None -> false in

  let open Ltac_plugin.Tacexpr in
  let@ raw_tactic_expr = Syntax_node.get_node_raw_tactic_expr x in

  match raw_tactic_expr.v with
  | TacArg (TacCall call_arg) ->
      let call_qualid, _ = call_arg.v in
      let call_qualid_str = Libnames.string_of_qualid call_qualid in
      call_qualid_str = "prolong"
  | _ -> false

let prolong_arg_to_string
    (x : Ltac_plugin.Tacexpr.r_dispatch Ltac_plugin.Tacexpr.gen_tactic_arg) :
    string option =
  match x with
  | Ltac_plugin.Tacexpr.Reference reference ->
      Some (Libnames.string_of_qualid reference)
  | _ -> None

(** If [tacexpr] is exactly a TacArg(TacCall ...), rename the called qualid. *)
let replace_taccall_tacarg_in_tacexpr (old_tac_call_name : string)
    (new_tac_call_name : string) (tacexpr : Ltac_plugin.Tacexpr.raw_tactic_expr)
    : Ltac_plugin.Tacexpr.raw_tactic_expr =
  let open Ltac_plugin.Tacexpr in
  match tacexpr.v with
  | TacArg (TacCall call_arg) ->
      let old_call_qualid, old_call_args = call_arg.v in
      let old_call_qualid_str = Libnames.string_of_qualid old_call_qualid in
      if old_call_qualid_str = old_tac_call_name then
        let new_tac_call_name_qualid =
          Libnames.qualid_of_string new_tac_call_name
        in
        let new_tac_call =
          CAst.make (new_tac_call_name_qualid, old_call_args)
        in
        TacArg (TacCall new_tac_call) |> CAst.make
      else tacexpr
  | _ -> tacexpr

let replace_prolong_by_segment_cons (x : Ltac_plugin.Tacexpr.raw_tactic_expr) :
    Ltac_plugin.Tacexpr.raw_tactic_expr =
  match x.v with
  | TacArg (TacCall call_arg) ->
      let call_qualid, _ = call_arg.v in
      let call_qualid_str = Libnames.string_of_qualid call_qualid in
      if call_qualid_str = "prolong" then
        let _, fun_args = call_arg.v in
        let args_str_opt = List.map prolong_arg_to_string fun_args in
        let args_str = List.map Option.get args_str_opt in
        match args_str with
        | [ args0; args1; args2; args3; args4 ] ->
            let segment_construction_str =
              Printf.sprintf
                "apply (by_segment_construction %s %s %s %s); [solve_stable | \
                 intros [%s [?H%s ?H%s]]]."
                args0 args1 args3 args4 args2 args1 args3
            in
            let segment_construction_raw_tactic_expr =
              Syntax_node.string_to_raw_tactic_expr segment_construction_str
            in
            Result.fold
              ~ok:(fun a -> a)
              ~error:(fun e -> x)
              segment_construction_raw_tactic_expr
        | _ -> x
      else x
  | _ -> x

let map_assert_constr_expr
    (f : Constrexpr.constr_expr -> Constrexpr.constr_expr)
    (tacexpr : Ltac_plugin.Tacexpr.raw_tactic_expr) :
    Ltac_plugin.Tacexpr.raw_tactic_expr =
  let open Ltac_plugin.Tacexpr in
  match tacexpr.v with
  | TacAtom (TacAssert (a, b, c, d, asrt)) ->
      TacAtom (TacAssert (a, b, c, d, Constrexpr_map.constr_expr_map f asrt))
      |> CAst.make
  | _ -> tacexpr

let map_raw_tactic_expr_in_node
    (f :
      Ltac_plugin.Tacexpr.raw_tactic_expr -> Ltac_plugin.Tacexpr.raw_tactic_expr)
    (node : Syntax_node.t) : transformation_step option =
  let+ raw_tac_expr = Syntax_node.get_node_raw_tactic_expr node in
  let raw_expr_mapped = Tacexpr_map.tacexpr_map f raw_tac_expr in
  if not (raw_tac_expr = raw_expr_mapped) then
    let selector = Syntax_node.get_node_goal_selector_opt node in
    let+ new_node =
      Syntax_node.raw_tactic_expr_to_syntax_node raw_expr_mapped ?selector
        node.range.start
      |> Result.to_option
    in
    Some (Replace (node.id, new_node))
  else None

let map_assert_in_node (f : Constrexpr.constr_expr -> Constrexpr.constr_expr)
    (node : Syntax_node.t) : transformation_step option =
  map_raw_tactic_expr_in_node (map_assert_constr_expr f) node

let replace_taccall_tacarg_in_node (old_tac_call_name : string)
    (new_tac_call_name : string) (node : Syntax_node.t) :
    transformation_step option =
  map_raw_tactic_expr_in_node
    (replace_taccall_tacarg_in_tacexpr old_tac_call_name new_tac_call_name)
    node

let get_cref_qualid (x : Constrexpr.constr_expr) : Libnames.qualid option =
  match x.v with Constrexpr.CRef (qualid, _) -> Some qualid | _ -> None

let is_constrexpr_eq_dec_points_a_b (x : Constrexpr.constr_expr) : bool =
  match x.v with
  | Constrexpr.CApp (func, _) ->
      Option.map Libnames.string_of_qualid (get_cref_qualid func)
      = Some "eq_dec_points"
  | _ -> false

let get_func_args (x : Constrexpr.constr_expr) : Constrexpr.constr_expr list =
  match x.v with Constrexpr.CApp (_, args) -> List.map fst args | _ -> []

let replace_induction_by_stab_eq_point (x : Ltac_plugin.Tacexpr.raw_tactic_expr)
    : Ltac_plugin.Tacexpr.raw_tactic_expr =
  match x.v with
  | TacAtom (TacInductionDestruct (true, false, ([ induction_clause_head ], _)))
    -> (
      let (tac_flag, core_destruction_arg), _, _ = induction_clause_head in
      match core_destruction_arg with
      | ElimOnConstr (constrexpr, NoBindings)
        when is_constrexpr_eq_dec_points_a_b constrexpr -> (
          let fun_args = get_func_args constrexpr in
          let fun_args_str =
            List.map
              (fun x ->
                get_cref_qualid x |> Option.get |> Libnames.string_of_qualid)
              fun_args
          in
          let stab_eq_str =
            "stab_eq_point " ^ String.concat " " fun_args_str ^ "; intros ?H."
          in
          let raw_tac_expr_stab_eq =
            Syntax_node.string_to_raw_tactic_expr stab_eq_str
          in
          match raw_tac_expr_stab_eq with Ok expr -> expr | Error _ -> x)
      | _ -> x)
  | _ -> x

let map_definition_body (f : Constrexpr.constr_expr -> Constrexpr.constr_expr)
    (x : Syntax_node.t) : transformation_step option =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).v.expr with
      | VernacSynPure
          (Vernacexpr.VernacDefinition
             ( (discharge, definition_object_kind),
               (name_decl : Constrexpr.name_decl),
               expr )) -> (
          match expr with
          | ProveBody _ -> None
          | DefineBody (binders, raw_red_expr_opt, expr1, opt_expr) ->
              let new_expr = Constrexpr_map.constr_expr_map f expr1 in
              if not (Constrexpr_ops.constr_expr_eq expr1 new_expr) then
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
      | _ -> None)
  | None -> None

let replace_fun_name_in_definition (old_fun_name : string)
    (new_fun_name : string) (x : Syntax_node.t) : transformation_step option =
  map_definition_body
    (replace_fun_name_in_constrexpr old_fun_name new_fun_name)
    x

let replace_notation_in_definition (old_notation : string)
    (new_notation : string) (x : Syntax_node.t) : transformation_step option =
  map_definition_body
    (replace_notation_in_constrexpr old_notation new_notation)
    x

let add_node_after_require (doc : Rocq_document.t) (node : Syntax_node.t) :
    transformation_step option =
  let+ last_require =
    List.find_opt Syntax_node.is_syntax_node_require (List.rev doc.elements)
  in
  Some (Attach (node, LineAfter, last_require.id))

let get_proof_conclusion (p : Proof.t) : Constrexpr.constr_expr option =
  let ( let+ ) = Option.bind in
  let+ components = Proof.get_theorem_components p in
  let expr = components.expr in
  let rec get_conclusion (expr : Constrexpr.constr_expr) =
    match expr.v with
    | Constrexpr.CProdN (_binders, body) -> get_conclusion body
    | Constrexpr.CLetIn (_, _, _, body) -> get_conclusion body
    | Constrexpr.CNotation
        ( opt_scope,
          (notation_entry, notation_key),
          (args, _args_lists, _pats, _lbnds) ) ->
        if notation_key = "_ -> _" then (
          match args with
          | [ left; right ] -> get_conclusion right
          | _ ->
              Logs.debug (fun m -> m "this is NOT supposed to happens");
              None)
        else Some expr
    | _ -> Some expr
  in
  get_conclusion expr

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

let get_syntax_node_assert_expr (x : Syntax_node.t) =
  match Syntax_node.get_node_raw_atomic_tactic_expr x with
  | Some (TacAssert (false, true, _, _, expr)) -> Some expr
  | _ -> None

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
                    else Attach (new_node_el, attach_position, id_el)
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

let replace_assert_by_stab_assert (doc : Rocq_document.t) (x : Syntax_node.t) :
    (transformation_step list, Error.t) result =
  let dummy_start : Code_point.t = { line = 0; character = 0 } in
  let raw_tactic_expr = Syntax_node.get_node_raw_tactic_expr x in
  let raw_atomic_expr =
    Option.map Ltac.get_raw_atomic_tactic_expr raw_tactic_expr
  in
  match Option.flatten raw_atomic_expr with
  | Some
      (Ltac_plugin.Tacexpr.TacAssert (false, true, by_content, _, assert_expr))
    -> (
      let token = Coq.Limits.Token.create () in
      let* state_assert_before = Runner.get_init_state doc x token in
      let* state_assert_after = Runner.run_node token state_assert_before x in
      let old_goals_vars =
        Runner.reified_goals_at_state token state_assert_before
        |> List.map Runner.get_hypothesis_names
        |> Option.make
      in

      let new_goals_vars =
        Runner.reified_goals_at_state token state_assert_after
        |> List.map Runner.get_hypothesis_names
        |> Option.make
      in
      let* new_vars =
        get_new_vars old_goals_vars new_goals_vars
        |> Option_utils.to_result
             ~none:
               (Error.format_to_or_error "Error getting new vars for node %s"
                  (Syntax_node.repr x))
      in

      let assert_generated_name =
        if Syntax_node.is_syntax_node_assert_by x then
          List.nth new_vars 0 |> List.hd
        else List.nth new_vars 1 |> List.hd
      in

      let assert_expr_str = constrexpr_to_string assert_expr in
      Logs.debug (fun m -> m "assert_expr_str: %s" assert_expr_str);
      let stab_assert_node_str =
        Printf.sprintf "stab_assert (%s: (%s))." assert_generated_name
          assert_expr_str
      in
      Logs.debug (fun m -> m "stab_assert_node_str: %s" stab_assert_node_str);
      let* stab_assert_node =
        Syntax_node.syntax_node_of_string stab_assert_node_str x.range.start
      in

      let* unNNnode = Syntax_node.syntax_node_of_string "unNN." dummy_start in
      match by_content with
      | Some (Some expr) ->
          let* tac_node =
            Syntax_node.raw_tactic_expr_to_syntax_node expr dummy_start
          in
          Ok
            [
              Replace (x.id, stab_assert_node);
              Attach (unNNnode, SameLine, stab_assert_node.id);
              Attach (tac_node, LineAfter, unNNnode.id);
            ]
      | _ ->
          Ok
            [
              Replace (x.id, stab_assert_node);
              Attach (unNNnode, SameLine, stab_assert_node.id);
            ])
  | _ -> Ok []

let get_definition_file_steps (doc : Rocq_document.t) :
    (transformation_step list, Error.t) result =
  let dummy_start : Code_point.t = { line = 0; character = 0 } in

  if Filename.basename doc.filename = "Definitions.v" then
    let first_require =
      List.find Syntax_node.is_syntax_node_require doc.elements
    in

    let* new_first_require =
      Syntax_node.syntax_node_of_string
        "Require Export GeoCoq.Algebraic.Counter_models.nD.independent_version."
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

let constructivize_doc (doc : Rocq_document.t) :
    (transformation_step list, Error.t) result =
  let token = Coq.Limits.Token.create () in
  let* proofs = Rocq_document.get_proofs doc in

  let conclusions = List.filter_map get_proof_conclusion proofs in
  List.iter
    (fun x ->
      let x_str = constrexpr_to_string x in
      Logs.debug (fun m -> m "%s" x_str))
    conclusions;

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
  let* definitions_file_specific_steps = get_definition_file_steps doc in

  let* replace_require_steps =
    List_utils.concat_map_result replace_require doc.elements
  in

  let* replace_context_steps =
    List_utils.concat_map_result replace_context doc.elements
  in

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
    List.filter_map
      (replace_fun_name_in_proof_proposition "Bet" "BetL")
      proofs_stage_two
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

  let* stage_four_doc =
    Rocq_document.apply_transformations_steps steps_stage_three stage_three_doc
  in

  let f_assert =
   fun x ->
    replace_fun_name_in_constrexpr "Bet" "BetL" x
    |> replace_notation_in_constrexpr "_ \\/ _" "_ \\_/ _"
  in

  let replace_bet_by_betl_and_or_by_cons_or_in_assert_steps =
    List.filter_map (map_assert_in_node f_assert) stage_four_doc.elements
  in

  let steps_stage_four =
    replace_bet_by_betl_and_or_by_cons_or_in_assert_steps
  in

  let* stage_five_doc =
    Rocq_document.apply_transformations_steps steps_stage_four stage_four_doc
  in

  let replace_cong_by_econg_steps =
    List.filter_map
      (replace_taccall_tacarg_in_node "Cong" "eCong")
      stage_five_doc.elements
  in

  let replace_induction_by_stab_eq_point_steps =
    List.filter_map
      (map_raw_tactic_expr_in_node replace_induction_by_stab_eq_point)
      stage_five_doc.elements
  in

  let steps_stage_five =
    replace_cong_by_econg_steps @ replace_induction_by_stab_eq_point_steps
  in

  let* stage_six_doc =
    Rocq_document.apply_transformations_steps steps_stage_five stage_five_doc
  in

  let prolong_to_segment_cons_steps =
    List.filter_map
      (map_raw_tactic_expr_in_node replace_prolong_by_segment_cons)
      stage_six_doc.elements
  in

  (* let* assert_to_stab_assert_steps = *)
  (*   List_utils.concat_map_result *)
  (*     (replace_assert_by_stab_assert stage_six_doc) *)
  (*     stage_six_doc.elements *)
  (* in *)
  let steps_stage_six = prolong_to_segment_cons_steps in
  let res =
    Ok
      (update_replaces
         (List.concat
            [
              steps_stage_zero;
              steps_stage_one;
              steps_stage_two;
              steps_stage_three;
              steps_stage_four;
              steps_stage_five;
              steps_stage_six;
            ]))
  in
  res
