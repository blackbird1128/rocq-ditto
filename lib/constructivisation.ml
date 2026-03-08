open Proof
open Vernacexpr
open Constructivisation_data
open Constrexpr_utils

let ( let* ) = Result.bind
let ( let+ ) = Option.bind

module Syntax_nodeSet = Set.Make (struct
  type t = Syntax_node.t

  let compare = Syntax_node.compare
end)

module StringSet = Set.Make (String)

let replace_require (x : Syntax_node.t) :
    (transformation_step list, Error.t) result =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).v.expr with
      | VernacSynterp
          (VernacRequire
             (option_libname, export_with_cats_opt, libnames_import_list)) -> (
          match List.nth_opt libnames_import_list 0 with
          | Some (qualid, import_filter) ->
              let qualid_str = Libnames.string_of_qualid qualid in
              if String.starts_with ~prefix:"GeoCoq.Main.Tarski_dev" qualid_str
              then
                let _, postfix =
                  String_utils.split_prefix "GeoCoq.Main.Tarski_dev" qualid_str
                  |> Option.get
                in

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
              else if
                String.starts_with ~prefix:"GeoCoq.Axioms.Definitions"
                  qualid_str
              then
                let* new_node =
                  Syntax_node.syntax_node_of_string
                    "Require Export GeoCoq.Constructive.Definitions."
                    x.range.start
                in
                Ok [ Replace (x.id, new_node) ]
              else Ok []
          | None ->
              Error.format_to_or_error
                "Error getting libnames_import_list in %s" (Syntax_node.repr x))
      | _ -> Ok [])
  | None -> Ok []

let replace_contexts (doc : Rocq_document.t) :
    (transformation_step list, Error.t) result =
  let new_context_str : string =
    "Context {Pred : predicates}\n\
    \        {ITn : independent_Tarski_neutral_dimensionless Pred}\n\
    \        {ES : Eq_stability Pred ITn}\n\
    \        {Dim : dimension}\n\
    \        {ITnD : @independent_Tarski_nD Pred ITn (incr (incr Dim))}."
  in
  let rec aux (nodes : Syntax_node.t list) (prev_was_context : bool)
      (acc : transformation_step list) :
      (transformation_step list, Error.t) result =
    match nodes with
    | [] -> Ok (List.rev acc)
    | node :: tail ->
        if Syntax_node.is_syntax_node_context node then
          if prev_was_context then aux tail true (Remove node.id :: acc)
          else
            let* new_context_node =
              Syntax_node.syntax_node_of_string new_context_str node.range.start
            in
            aux tail true (Replace (node.id, new_context_node) :: acc)
        else aux tail false acc
  in
  aux doc.elements false []

let attach_prelude_to_chapter (doc : Rocq_document.t) (chapter_name : string) :
    (transformation_step list, Error.t) result =
  let dummy_start : Code_point.t = { line = 0; character = 0 } in
  if Filename.basename doc.filename = chapter_name then
    let last_require_opt =
      List_utils.find_last_opt Syntax_node.is_syntax_node_require doc.elements
    in
    match last_require_opt with
    | Some last_require ->
        let* prelude_node =
          Syntax_node.syntax_node_of_string
            "Require Export GeoCoq.Constructive.Prelude." dummy_start
        in
        Ok [ Attach (prelude_node, LineAfter, last_require.id) ]
    | None ->
        Error.string_to_or_error
          "Attach prelude: No Require node was found in chapter 2, check \
           assumptions !"
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

  let matches_ref q = Libnames.qualid_eq q old_q in

  match term.v with
  | Constrexpr.CRef (q, instance_expr_opt) when matches_ref q ->
      CAst.make (Constrexpr.CRef (new_q, instance_expr_opt))
  | Constrexpr.CAppExpl ((q, instance_expr_opt), l) when matches_ref q ->
      CAst.make (Constrexpr.CAppExpl ((new_q, instance_expr_opt), l))
  | _ -> term

let replace_bet_and_cong_in_constrexpr (term : Constrexpr.constr_expr) :
    Constrexpr.constr_expr =
  term
  |> replace_fun_name_in_constrexpr "Bet" "BetC"
  |> replace_fun_name_in_constrexpr "Cong" "CongC"

let replace_notation_in_proof_proposition (old_notation : string)
    (new_notation : string) (x : Proof.t) : transformation_step option =
  map_proof_proposition
    (replace_notation_in_constrexpr old_notation new_notation)
    x

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

let prolong_arg_to_string
    (x : Ltac_plugin.Tacexpr.r_dispatch Ltac_plugin.Tacexpr.gen_tactic_arg) :
    string option =
  match x with
  | Ltac_plugin.Tacexpr.Reference reference ->
      Some (Libnames.string_of_qualid reference)
  | _ -> None

let replace_prolong_by_segment_cons (x : Ltac_plugin.Tacexpr.raw_tactic_expr) :
    Ltac_plugin.Tacexpr.raw_tactic_expr =
  match x.v with
  | TacArg (TacCall call_arg) ->
      let call_qualid, fun_args = call_arg.v in
      if String.equal (Libnames.string_of_qualid call_qualid) "prolong" then
        let args_str_opt = List.map prolong_arg_to_string fun_args in
        match List_utils.option_all args_str_opt with
        | Some [ args0; args1; args2; args3; args4 ] -> (
            let segment_construction_str =
              Printf.sprintf
                "stab_destruct (by_segment_construction %s %s %s %s) as [%s \
                 [?H ?H]]."
                args0 args1 args3 args4
                args2 (* args1 args3 used in ? H before *)
            in
            match
              Syntax_node.string_to_raw_tactic_expr segment_construction_str
            with
            | Ok a -> a
            | Error _ -> x)
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

let map_tacdef_bodies_in_node
    (f :
      Ltac_plugin.Tacexpr.raw_tactic_expr -> Ltac_plugin.Tacexpr.raw_tactic_expr)
    (g : Constrexpr.constr_expr -> Constrexpr.constr_expr)
    (node : Syntax_node.t) : transformation_step option =
  let+ tacdef_bodies = Syntax_node.get_node_tacdef_bodies node in
  let tacdef_bodies_mapped =
    List.map
      (fun (body : Ltac_plugin.Tacexpr.tacdef_body) ->
        match body with
        | Ltac_plugin.Tacexpr.TacticDefinition (name, tacexpr) ->
            Ltac_plugin.Tacexpr.TacticDefinition
              (name, Tacexpr_map.tacexpr_map_with_constr f g tacexpr)
        | Ltac_plugin.Tacexpr.TacticRedefinition (name, tacexpr) ->
            Ltac_plugin.Tacexpr.TacticRedefinition
              (name, Tacexpr_map.tacexpr_map_with_constr f g tacexpr))
      tacdef_bodies
  in

  if not (List.equal ( = ) tacdef_bodies tacdef_bodies_mapped) then
    let+ new_node =
      Syntax_node.tacdef_body_list_to_syntax_node tacdef_bodies_mapped
        node.range.start
      |> Result.to_option
    in

    Some (Replace (node.id, new_node))
  else None

let replace_taccall_tacarg_in_node (old_tac_call_name : string)
    (new_tac_call_name : string) (node : Syntax_node.t) :
    transformation_step option =
  Transformations.map_raw_tactic_expr_in_node
    (replace_taccall_tacarg_in_tacexpr old_tac_call_name new_tac_call_name)
    node

let get_tac_generic_genarg
    (x : Ltac_plugin.Tacexpr.r_dispatch Ltac_plugin.Tacexpr.gen_tactic_arg) :
    Genarg.rlevel Genarg.generic_argument option =
  match x with
  | Ltac_plugin.Tacexpr.TacGeneric (_, genarg) -> Some genarg
  | _ -> None

let replace_decompose_or_with_decompose_stab_or
    (x : Ltac_plugin.Tacexpr.raw_tactic_expr) :
    Ltac_plugin.Tacexpr.raw_tactic_expr =
  match x.v with
  | TacAlias (alias, [ decomposed_args; hypothesis ])
    when String.starts_with
           (Names.KerName.to_string alias)
           ~prefix:"Corelib.Init.Ltac.decompose_[_#_]_#_" -> (
      let decomposed_args_genarg =
        get_tac_generic_genarg decomposed_args |> Option.get
      in
      let args_str =
        Raw_gen_args_converter.constr_expr_list_of_raw_generic_argument
          decomposed_args_genarg
        |> Option.map (List.map constrexpr_to_string)
      in
      match args_str with
      | Some [ "or" ] ->
          let hypothesis_genarg =
            get_tac_generic_genarg hypothesis |> Option.get
          in
          let hypothesis_str =
            Raw_gen_args_converter.constr_expr_of_raw_generic_argument
              hypothesis_genarg
            |> Option.get |> constrexpr_to_string
          in

          let decompose_stab_or_raw_tac_expr =
            Syntax_node.string_to_raw_tactic_expr
              ("decompose_stab_or " ^ hypothesis_str ^ ".")
            |> Result.get_ok
          in

          decompose_stab_or_raw_tac_expr
      | Some [ "or"; "and" ] | Some [ "and"; "or" ] ->
          let hypothesis_genarg =
            get_tac_generic_genarg hypothesis |> Option.get
          in
          let hypothesis_str =
            Raw_gen_args_converter.constr_expr_of_raw_generic_argument
              hypothesis_genarg
            |> Option.get |> constrexpr_to_string
          in

          let decompose_stab_or_raw_tac_expr =
            Syntax_node.string_to_raw_tactic_expr
              ("decompose_stab_or_and " ^ hypothesis_str ^ ".")
            |> Result.get_ok
          in

          decompose_stab_or_raw_tac_expr
      | _ -> x)
  | _ -> x

let replace_elim_with_stab_eq_point (x : Ltac_plugin.Tacexpr.raw_tactic_expr) :
    Ltac_plugin.Tacexpr.raw_tactic_expr =
  match x.v with
  | TacAtom (TacElim (_, binding_args, _)) ->
      let _, (elim_expr, _) = binding_args in
      if is_constrexpr_c_app_named elim_expr "eq_dec_points" then
        let fun_args = get_func_args elim_expr in
        let fun_args_str_opt =
          List.map
            (fun x -> get_cref_qualid x |> Option.map Libnames.string_of_qualid)
            fun_args
        in
        match List_utils.option_all fun_args_str_opt with
        | Some fun_args_str -> (
            let stab_eq_str =
              "stab_eq_point  " ^ String.concat " " fun_args_str ^ "."
            in

            match Syntax_node.string_to_raw_tactic_expr stab_eq_str with
            | Ok expr -> expr
            | Error _ -> x)
        | None -> x
      else x
  | _ -> x

type stab_kind =
  | Inner_pasch
  | Segment_construction
  | Eq_Dec_Points
  | Stab_destruct_as_or
  | Stab_destruct_no_args

let dummy_tactic_for_kind = function
  | Inner_pasch -> "stab_destruct (by_inner_pasch A B C D X X X) as [I []]."
  | Segment_construction ->
      "stab_destruct (by_segment_construction A B C D) as [I []]."
  | Eq_Dec_Points -> "stab_destruct (by_eq_dec_points B C)."
  | Stab_destruct_no_args -> "stab_destruct H."
  | Stab_destruct_as_or -> "stab_destruct H as [HL|HR]."

let compute_alias_kername (k : stab_kind) : Names.KerName.t option =
  let s = dummy_tactic_for_kind k in
  match Syntax_node.string_to_raw_tactic_expr s with
  | Error _ -> None
  | Ok raw -> Ltac.get_alias_kername raw

let inner_pasch_alias_kn : Names.KerName.t option Lazy.t =
  lazy (compute_alias_kername Inner_pasch)

let segment_construction_alias_kn : Names.KerName.t option Lazy.t =
  lazy (compute_alias_kername Segment_construction)

let eq_dec_points_alias_kn : Names.KerName.t option Lazy.t =
  lazy (compute_alias_kername Eq_Dec_Points)

let stab_destruct_as_or_alias_kn : Names.KerName.t option Lazy.t =
  lazy (compute_alias_kername Stab_destruct_as_or)

let stab_destruct_no_args_alias_kn : Names.KerName.t option Lazy.t =
  lazy (compute_alias_kername Stab_destruct_no_args)

let get_alias_kn = function
  | Inner_pasch -> Lazy.force inner_pasch_alias_kn
  | Segment_construction -> Lazy.force segment_construction_alias_kn
  | Eq_Dec_Points -> Lazy.force eq_dec_points_alias_kn
  | Stab_destruct_as_or -> Lazy.force stab_destruct_as_or_alias_kn
  | Stab_destruct_no_args -> Lazy.force stab_destruct_no_args_alias_kn

let constrexpr_to_stab_destruct_fun_name (c : Constrexpr.constr_expr) =
  if is_constrexpr_c_app_named c "inner_pasch" then get_alias_kn Inner_pasch
  else if is_constrexpr_c_app_named c "segment_construction" then
    get_alias_kn Segment_construction
  else if is_constrexpr_c_app_named c "eq_dec_points" then
    get_alias_kn Eq_Dec_Points
  else None

let replace_destruct_fun_with_stab_destruct
    (x : Ltac_plugin.Tacexpr.raw_tactic_expr) :
    Ltac_plugin.Tacexpr.raw_tactic_expr =
  match x.v with
  | TacAtom (TacInductionDestruct (false, false, ([ destruct_target ], _))) -> (
      let (_, core_destruction_arg), intro_pattern_naming_expr, _ =
        destruct_target
      in
      match core_destruction_arg with
      | ElimOnIdent h -> (
          match intro_pattern_naming_expr with
          | _, Some (ArgArg intro_or_and_pattern) ->
              let h_constrexpr : Constrexpr.constr_expr =
                Constrexpr.CRef (Libnames.qualid_of_lident h, None) |> CAst.make
              in

              let intro_pattern_action_expr =
                Tactypes.IntroOrAndPattern intro_or_and_pattern.v
              in
              let intro_pattern_expr =
                Tactypes.IntroAction intro_pattern_action_expr |> CAst.make
              in

              let open_constr_arg =
                Raw_gen_args_converter.raw_generic_argument_of_open_constr
                  h_constrexpr
              in

              let intro_pattern_arg =
                Raw_gen_args_converter.raw_generic_argument_of_intro_pattern
                  intro_pattern_expr
              in

              let ker_name = get_alias_kn Stab_destruct_as_or |> Option.get in

              let stab_destruct_args =
                List.map
                  (fun x -> Ltac_plugin.Tacexpr.TacGeneric (None, x))
                  [ open_constr_arg; intro_pattern_arg ]
              in

              Ltac_plugin.Tacexpr.TacAlias (ker_name, stab_destruct_args)
              |> CAst.make
          | None, None ->
              let h_constrexpr : Constrexpr.constr_expr =
                Constrexpr.CRef (Libnames.qualid_of_lident h, None) |> CAst.make
              in

              let open_constr_arg =
                Raw_gen_args_converter.raw_generic_argument_of_open_constr
                  h_constrexpr
              in
              let stab_destruct_args =
                List.map
                  (fun x -> Ltac_plugin.Tacexpr.TacGeneric (None, x))
                  [ open_constr_arg ]
              in

              let ker_name = get_alias_kn Stab_destruct_no_args |> Option.get in

              Ltac_plugin.Tacexpr.TacAlias (ker_name, stab_destruct_args)
              |> CAst.make
          | _ -> x)
      | ElimOnConstr (constrexpr, NoBindings) -> (
          match constrexpr_to_stab_destruct_fun_name constrexpr with
          | Some kername -> (
              let fun_args = get_func_args constrexpr in
              let fun_args_str_opt =
                List.map
                  (fun x ->
                    get_cref_qualid x |> Option.map Libnames.string_of_qualid)
                  fun_args
                |> List_utils.option_all
              in

              match intro_pattern_naming_expr with
              | _, Some (ArgArg intro_or_and_pattern) ->
                  let fun_args_name_id_arg =
                    Option.map
                      (List.map (fun x ->
                           Names.Id.of_string x
                           |> Raw_gen_args_converter.raw_generic_argument_of_id))
                      fun_args_str_opt
                    |> Option.get
                  in

                  let intro_action =
                    Tactypes.IntroOrAndPattern intro_or_and_pattern.v
                  in
                  let intro_pattern_expr =
                    Tactypes.IntroAction intro_action |> CAst.make
                  in
                  let intro_arg =
                    Raw_gen_args_converter.raw_generic_argument_of_intro_pattern
                      intro_pattern_expr
                  in

                  let stab_destruct_args =
                    List.map
                      (fun x -> Ltac_plugin.Tacexpr.TacGeneric (None, x))
                      (fun_args_name_id_arg @ [ intro_arg ])
                  in

                  Ltac_plugin.Tacexpr.TacAlias (kername, stab_destruct_args)
                  |> CAst.make
              | _, None ->
                  let stab_destruct_args =
                    List.map
                      (fun x -> Ltac_plugin.Tacexpr.TacGeneric (None, x))
                      [
                        constrexpr
                        |> Raw_gen_args_converter
                           .raw_generic_argument_of_open_constr;
                      ]
                  in
                  Ltac_plugin.Tacexpr.TacAlias (kername, stab_destruct_args)
                  |> CAst.make
              | _ -> x)
          | None -> x)
      | _ -> x)
  | _ -> x

let replace_induction_by_stab_eq_point (x : Ltac_plugin.Tacexpr.raw_tactic_expr)
    : Ltac_plugin.Tacexpr.raw_tactic_expr =
  match x.v with
  | TacAtom (TacInductionDestruct (true, false, ([ induction_clause_head ], _)))
    -> (
      let (_, core_destruction_arg), _, _ = induction_clause_head in
      match core_destruction_arg with
      | ElimOnConstr (constrexpr, NoBindings)
        when is_constrexpr_c_app_named constrexpr "eq_dec_points" -> (
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

          match Syntax_node.string_to_raw_tactic_expr stab_eq_str with
          | Ok expr -> expr
          | Error _ -> x)
      | _ -> x)
  | _ -> x

let map_definition_body (f : Constrexpr.constr_expr -> Constrexpr.constr_expr)
    (x : Syntax_node.t) : transformation_step option =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).v.expr with
      | VernacSynPure
          (Vernacexpr.VernacDefinition
             ((discharge, definition_object_kind), name_decl, expr)) -> (
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

let constrexpr_contains_exists (x : Constrexpr.constr_expr) : bool =
  Constrexpr_fold.exists
    (fun expr ->
      match expr.v with
      | Constrexpr.CNotation (_, (_, notation_key), _) ->
          notation_key = "exists _ .. _ , _"
      | _ -> false)
    x

let collect_definitions_containing_exists (nodes : Syntax_node.t list) :
    string list =
  let rec aux nodes (acc_list : string list) (acc_set : StringSet.t) =
    match nodes with
    | [] -> List.rev acc_list
    | x :: tail -> begin
        match
          ( Syntax_node.get_definition_constrexpr x,
            Syntax_node.get_definition_name x )
        with
        | Some expr, Some name ->
            let references_prev =
              get_fun_names_in_constrexpr expr
              |> List.exists (fun q ->
                  StringSet.mem (Libnames.string_of_qualid q) acc_set)
            in
            if constrexpr_contains_exists expr || references_prev then
              aux tail (name :: acc_list) (StringSet.add name acc_set)
            else aux tail acc_list acc_set
        | _ -> aux tail acc_list acc_set
      end
  in
  aux nodes [] StringSet.empty

let is_proof_about_exists (p : Proof.t) : bool =
  match Proof.get_proof_conclusion p with
  | None -> false
  | Some conclusion ->
      if constrexpr_contains_exists conclusion then true
      else
        get_fun_names_in_constrexpr conclusion
        |> List.exists (fun q ->
            let s = Libnames.string_of_qualid q in
            List.mem s definitions_with_exists)

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
        Runner.get_new_vars old_goals_vars new_goals_vars
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
      let stab_assert_node_str =
        Printf.sprintf "stab_assert (%s: (%s))." assert_generated_name
          assert_expr_str
      in

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

let collect_named_section_ids (section_names : string list)
    (doc : Rocq_document.t) : (Uuidm.t list, Error.t) result =
  let section_marker (node : Syntax_node.t) :
      [ `Begin of string | `End of string ] option =
    match Syntax_node.get_vernac_expr_gen node with
    | Some (Vernacexpr.VernacSynterp expr) -> (
        match expr with
        | Vernacexpr.VernacBeginSection ident ->
            Some (`Begin (Names.Id.to_string ident.v))
        | Vernacexpr.VernacEndSegment ident ->
            Some (`End (Names.Id.to_string ident.v))
        | _ -> None)
    | _ -> None
  in
  let is_target name = List.exists (String.equal name) section_names in
  let rec aux nodes (current : string option) acc =
    match nodes with
    | [] -> Ok (current, List.rev acc)
    | node :: tail -> begin
        match current with
        | None -> (
            match section_marker node with
            | Some (`Begin name) when is_target name ->
                aux tail (Some name) (node.id :: acc)
            | _ -> aux tail None acc)
        | Some name ->
            let acc' = node.id :: acc in
            begin match section_marker node with
            | Some (`End end_name) when String.equal end_name name ->
                aux tail None acc'
            | _ -> aux tail (Some name) acc'
            end
      end
  in
  let* open_section, ids = aux doc.elements None [] in
  match open_section with
  | None -> Ok ids
  | Some name ->
      Error.format_to_or_error "Unclosed section while removing: %s" name

let remove_named_sections (section_names : string list) (doc : Rocq_document.t)
    : (transformation_step list, Error.t) result =
  let* ids = collect_named_section_ids section_names doc in
  Ok (List.map (fun id -> Remove id) ids)

let prove_dec_using_solve_dec (_ : Rocq_document.t) (proof : Proof.t) :
    (transformation_step list, Error.t) result =
  let ( let* ) = Result.bind in
  let dummy_start : Code_point.t = { line = 0; character = 0 } in
  let remove_all_steps_except_qed =
    List.filter_map
      (fun (step : Syntax_node.t) ->
        if Syntax_node.node_can_close_proof step then None
        else Some (Remove step.id))
      proof.proof_steps
  in

  let* solve_dec_node =
    Syntax_node.syntax_node_of_string "solve_dec." dummy_start
  in

  Ok
    (remove_all_steps_except_qed
    @ [ Attach (solve_dec_node, LineAfter, proof.proposition.id) ])

let destruction_arg_to_string
    (x : Constrexpr.constr_expr Tactypes.with_bindings Tactics.destruction_arg)
    : string =
  let _, with_bindings = x in
  match with_bindings with
  | Tactics.ElimOnConstr constr ->
      let constr_expr, _ = constr in
      Constrexpr_utils.constrexpr_to_string constr_expr
  | Tactics.ElimOnIdent ident ->
      let id = ident.v in
      Names.Id.to_string id
  | Tactics.ElimOnAnonHyp _ -> "anonymous"

let map_destruct_to_print_destruct (x : Ltac_plugin.Tacexpr.raw_tactic_expr) :
    Ltac_plugin.Tacexpr.raw_tactic_expr =
  let open Ltac_plugin in
  (* only treat destruct A. not destruct A, B for now *)
  match x.v with
  | Tacexpr.TacAtom
      (Tacexpr.TacInductionDestruct
         (false, false, ([ induction_clause_l ], _with_bindings))) -> (
      let destruction_arg, (_intro_pattern_naming_expr, _), _clause_expr_opt =
        induction_clause_l
      in
      let destruction_arg_str = destruction_arg_to_string destruction_arg in
      let print_tac_str =
        Printf.sprintf
          "let E := uconstr:(%s) in first [ generalize E; match goal with |- \
           ?T -> _ => idtac \"destructPat:\" E \":\" T end; intros _ | idtac  \
           \"destructPat:\" E; fail 1 \"does not typecheck\"]."
          destruction_arg_str
      in

      let print_tac_res = Syntax_node.string_to_raw_tactic_expr print_tac_str in
      match print_tac_res with
      | Ok print_tac ->
          let raw_tac = Tacexpr.TacThen (print_tac, x) |> CAst.make in
          raw_tac
      | Error _ -> x)
  | _ -> x

let transform_to_print_destruct (doc : Rocq_document.t) (proof : Proof.t) :
    (transformation_step list, Error.t) result =
  let token = Coq.Limits.Token.create () in
  Runner.fold_proof_with_state doc token
    (fun state acc node ->
      let* new_state = Runner.run_node token state node in
      match
        Transformations.map_raw_tactic_expr_in_node
          map_destruct_to_print_destruct node
      with
      | Some step -> Ok (new_state, step :: acc)
      | None -> Ok (new_state, acc))
    [] proof

let get_percentage_admitted (doc : Rocq_document.t) :
    (transformation_step list, Error.t) result =
  let* proofs = Rocq_document.get_proofs doc in
  let proofs_with_exists = List.filter is_proof_about_exists proofs in
  let proofs_length = List.length proofs in
  let proofs_with_exists_length = List.length proofs_with_exists in
  let percentage =
    if proofs_length = 0 then 0.0
    else
      Float.mul
        (Float.div
           (Float.of_int proofs_with_exists_length)
           (Float.of_int proofs_length))
        100.0
  in
  Printf.printf "%s\n%!" doc.filename;
  Printf.printf "admitted proofs: %d\n%!" proofs_with_exists_length;
  Printf.printf "total proofs: %d\n%!" proofs_length;
  Printf.printf "percentage: %.2f\n%!" percentage;

  Ok []

let get_proofs_named (proofs : Proof.t list) (names : string list) =
  List.filter
    (fun p ->
      let name = Proof.get_proof_name p in
      List.exists (fun x -> Option.equal String.equal name (Some x)) names)
    proofs

let definitions_of (d : Rocq_document.t) : Syntax_node.t list =
  List.filter Syntax_node.is_syntax_node_definition d.elements

type stage = {
  name : string;
  build_steps : Rocq_document.t -> (transformation_step list, Error.t) result;
}

let make_stage name build_steps = { name; build_steps }

let map_raw_tactic_expr_steps
    (f :
      Ltac_plugin.Tacexpr.raw_tactic_expr -> Ltac_plugin.Tacexpr.raw_tactic_expr)
    (doc : Rocq_document.t) : transformation_step list =
  List.filter_map (Transformations.map_raw_tactic_expr_in_node f) doc.elements

let replace_taccalls_in_tacexpr (renames : (string * string) list)
    (tacexpr : Ltac_plugin.Tacexpr.raw_tactic_expr) :
    Ltac_plugin.Tacexpr.raw_tactic_expr =
  List.fold_left
    (fun expr (old_name, new_name) ->
      replace_taccall_tacarg_in_tacexpr old_name new_name expr)
    tacexpr renames

let replace_taccalls_steps (renames : (string * string) list)
    (doc : Rocq_document.t) : transformation_step list =
  map_raw_tactic_expr_steps (replace_taccalls_in_tacexpr renames) doc

let apply_stage (doc : Rocq_document.t) (st : stage) =
  let* steps = st.build_steps doc in
  Rocq_document.apply_transformations_steps steps doc

let run_pipeline doc stages :
    (Rocq_document.t * transformation_step list, Error.t) result =
  List.fold_left
    (fun (acc : (Rocq_document.t * transformation_step list, Error.t) result) st
       ->
      let* doc_acc, steps_acc = acc in
      let* steps = st.build_steps doc_acc in
      let doc' = Rocq_document.apply_transformations_steps steps doc_acc in
      Result.product doc' (Ok (steps_acc @ steps)))
    (Ok (doc, []))
    stages

let constructivise_doc (doc : Rocq_document.t) :
    (transformation_step list, Error.t) result =
  let token = Coq.Limits.Token.create () in

  let dummy_start : Code_point.t = { line = 0; character = 0 } in

  let* require_prelude_node =
    Syntax_node.syntax_node_of_string
      "Require Import GeoCoq.Constructive.Prelude." dummy_start
  in

  let _preload_prelude =
    ignore
      (Runner.get_state_after doc.initial_state token [ require_prelude_node ])
    (* Require Geocoq.Constructive.Stable in the context for syntax_node_of_string ? this is a bit weird but for now, we need to inform Rocq of other export like this, this is not pure at all :[ *)
  in

  let blacklist_stage : stage =
    make_stage "blacklist_stage" (fun doc ->
        let* proofs = Rocq_document.get_proofs doc in

        let blacklisted_proofs = get_proofs_named proofs blacklisted_proofs in

        List_utils.concat_map_result
          (Transformations.admit_and_comment_proof_steps doc)
          blacklisted_proofs)
  in

  let stage_0 : stage =
    make_stage "stage0" (fun doc ->
        let* proofs = Rocq_document.get_proofs doc in

        let decidability_proofs : Proof.t list =
          get_proofs_named proofs decidability_lemmas
        in

        let* prove_decidability_proofs_steps =
          List_utils.concat_map_result
            (prove_dec_using_solve_dec doc)
            decidability_proofs
        in

        let* attach_prelude_to_chapter_two_steps =
          attach_prelude_to_chapter doc "Ch02_cong.v"
        in

        let* attach_prelude_to_chapter_twelwe_inted_dec_steps =
          attach_prelude_to_chapter doc "Ch12_parallel_inter_dec.v"
        in

        let* replace_require_steps =
          List_utils.concat_map_result replace_require doc.elements
        in

        let* replace_context_steps = replace_contexts doc in

        let definitions = definitions_of doc in

        let replace_or_by_constructive_or_in_proofs_steps =
          List.filter_map
            (replace_notation_in_proof_proposition "_ \\/ _" "_ \\_/ _")
            proofs
        in

        let replace_or_by_constructive_or_in_definitions_steps =
          List.filter_map
            ((fun (old_notation : string)
               (new_notation : string)
               (x : Syntax_node.t)
               :
               transformation_step option
             ->
               map_definition_body
                 (replace_notation_in_constrexpr old_notation new_notation)
                 x)
               "_ \\/ _" "_ \\_/ _")
            definitions
        in

        Ok
          (List.concat
             [
               prove_decidability_proofs_steps;
               attach_prelude_to_chapter_two_steps;
               attach_prelude_to_chapter_twelwe_inted_dec_steps;
               replace_require_steps;
               replace_context_steps;
               replace_or_by_constructive_or_in_proofs_steps;
               replace_or_by_constructive_or_in_definitions_steps;
             ]))
  in

  let blacklist_first_goal_ch10 : stage =
    make_stage "blacklist_comment_first_goal_ch10" (fun doc ->
        if String.ends_with ~suffix:"/Ch10_line_reflexivity.v" doc.filename then
          let* proofs = Rocq_document.get_proofs doc in
          let first_proof = List.hd proofs in
          Transformations.admit_and_comment_proof_steps doc first_proof
        else Ok [])
  in

  let stage_beeson_ch03 : stage =
    make_stage "stage_beeson_ch03" (fun doc ->
        if String.ends_with ~suffix:"/Ch03_bet.v" doc.filename then
          remove_named_sections [ "Beeson_1"; "Beeson_2" ] doc
        else Ok [])
  in

  let stage_1 : stage =
    make_stage "stage1" (fun doc ->
        let* proofs = Rocq_document.get_proofs doc in

        let proofs_with_exists = List.filter is_proof_about_exists proofs in

        let* admit_exists_proofs_steps =
          List_utils.concat_map_result
            (Transformations.admit_and_comment_proof_steps doc)
            proofs_with_exists
        in

        Ok admit_exists_proofs_steps)
  in

  let stage_2 : stage =
    make_stage "stage2" (fun doc ->
        let* proofs_stage_two = Rocq_document.get_proofs doc in

        let definitions_stage_two = definitions_of doc in

        let replace_bet_and_cong_by_cons_ver_in_proofs_steps =
          List.filter_map
            (map_proof_proposition replace_bet_and_cong_in_constrexpr)
            proofs_stage_two
        in

        let replace_bet_and_cong_by_cons_ver_definitions_steps =
          List.filter_map
            (map_definition_body replace_bet_and_cong_in_constrexpr)
            definitions_stage_two
        in

        let replace_tactic_calls =
          replace_taccalls_steps
            [
              ("left", "stab_left");
              ("right", "stab_right");
              ("tauto", "firstorder");
            ]
            doc
        in

        Ok
          (List.concat
             [
               replace_bet_and_cong_by_cons_ver_in_proofs_steps;
               replace_bet_and_cong_by_cons_ver_definitions_steps;
               replace_tactic_calls;
             ]))
  in

  let stage_3 =
    make_stage "stage3" (fun doc ->
        let f_assert =
          Fun.compose
            (replace_notation_in_constrexpr "_ \\/ _" "_ \\_/ _")
            replace_bet_and_cong_in_constrexpr
        in

        let replace_bet_by_betc_and_or_by_cons_or_in_assert_steps =
          List.filter_map
            (Transformations.map_raw_tactic_expr_in_node
               (map_assert_constr_expr f_assert))
            doc.elements
        in

        Ok replace_bet_by_betc_and_or_by_cons_or_in_assert_steps)
  in

  let stage_4 =
    make_stage "stage4" (fun doc ->
        let replace_induction_by_stab_eq_point_steps =
          map_raw_tactic_expr_steps replace_induction_by_stab_eq_point doc
        in

        let replace_elim_with_stab_eq_point_steps =
          map_raw_tactic_expr_steps replace_elim_with_stab_eq_point doc
        in

        Ok
          (List.concat
             [
               replace_induction_by_stab_eq_point_steps;
               replace_elim_with_stab_eq_point_steps;
             ]))
  in

  let stage_5 : stage =
    make_stage "stage5" (fun doc ->
        let prolong_to_segment_cons_steps =
          map_raw_tactic_expr_steps replace_prolong_by_segment_cons doc
        in

        Ok prolong_to_segment_cons_steps)
  in

  let stage_6 : stage =
    make_stage "stage6" (fun doc ->
        let decompose_or_to_stab_version_steps =
          map_raw_tactic_expr_steps replace_decompose_or_with_decompose_stab_or
            doc
        in

        Ok decompose_or_to_stab_version_steps)
  in

  let stage_7 : stage =
    make_stage "stage7" (fun doc ->
        let steps =
          map_raw_tactic_expr_steps replace_destruct_fun_with_stab_destruct doc
        in
        Ok steps)
  in

  let stage_8 : stage =
    make_stage "stage8" (fun doc ->
        let* proofs = Rocq_document.get_proofs doc in

        let proof_steps_node =
          List.concat_map (fun p -> p.proof_steps) proofs
        in

        let all_ltac_nodes_set =
          Syntax_nodeSet.of_list
            (List.filter Syntax_node.is_syntax_node_ltac doc.elements)
        in

        let proof_steps_set = Syntax_nodeSet.of_list proof_steps_node in

        let ltac_nodes =
          Syntax_nodeSet.diff all_ltac_nodes_set proof_steps_set
          |> Syntax_nodeSet.to_list
        in

        Ok
          (List.filter_map
             (fun x ->
               map_tacdef_bodies_in_node Fun.id
                 (Constrexpr_map.constr_expr_map
                    replace_bet_and_cong_in_constrexpr)
                 x)
             ltac_nodes))
  in

  (* let stage_11 : stage = *)
  (*   { *)
  (*     name = "stage11"; *)
  (*     build_steps = *)
  (*       (fun doc -> *)
  (*         List_utils.concat_map_result *)
  (*           (replace_assert_by_stab_assert doc) *)
  (*           doc.elements); *)
  (*   } *)
  (* in *)
  let* _, steps =
    run_pipeline doc
      [
        stage_0;
        stage_beeson_ch03;
        stage_1;
        stage_2;
        stage_3;
        stage_4;
        stage_5;
        stage_6;
        stage_7;
        stage_8;
        blacklist_first_goal_ch10;
        blacklist_stage;
        (* stage_11; *)
      ]
  in
  Ok (update_replaces steps)
