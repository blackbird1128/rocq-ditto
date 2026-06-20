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

let rewrite_qualid_prefix ~(old_prefix : string) ~(new_prefix : string)
    (qualid : Libnames.qualid) : Libnames.qualid option =
  let qualid_str = Libnames.string_of_qualid qualid in
  match String_utils.split_prefix old_prefix qualid_str with
  | Some (_, postfix) -> Some (Libnames.qualid_of_string (new_prefix ^ postfix))
  | None -> None

let rewrite_first_import ~(rules : (string * string) list)
    (libnames_import_list : (Libnames.qualid * import_filter_expr) list) :
    (Libnames.qualid * import_filter_expr) list option =
  match libnames_import_list with
  | [] -> None
  | (qualid, import_filter) :: rest ->
      let rec try_rules = function
        | [] -> None
        | (old_prefix, new_prefix) :: rules -> (
            match rewrite_qualid_prefix ~old_prefix ~new_prefix qualid with
            | Some new_qualid -> Some ((new_qualid, import_filter) :: rest)
            | None -> try_rules rules)
      in
      try_rules rules

let rebuild_require_node (x : Syntax_node.t)
    (option_libname : Libnames.qualid option)
    (export_with_cats_opt : export_with_cats option)
    (libnames_import_list : (Libnames.qualid * import_filter_expr) list) :
    (Syntax_node.t, Error.t) result =
  let new_expr =
    VernacSynterp
      (VernacRequire (option_libname, export_with_cats_opt, libnames_import_list))
  in
  let new_vernac_control = Syntax_node.mk_vernac_control new_expr in
  Ok
    (Syntax_node.syntax_node_of_coq_ast
       (Coq.Ast.of_coq new_vernac_control)
       x.range.start)

let replace_require (x : Syntax_node.t) :
    (transformation_step list, Error.t) result =
  let require_prefix_rules : (string * string) list =
    [
      ("GeoCoq.Main.Tarski_dev", "GeoCoq.Constructive");
      ("GeoCoq.Main.Annexes", "GeoCoq.Constructive.Annexes");
      ("GeoCoq.Main.Meta_theory.Models", "GeoCoq.Constructive.Tactic_instances");
      ( "GeoCoq.Main.Meta_theory.Dimension_axioms",
        "GeoCoq.Constructive.Dimension_axioms" );
      ( "GeoCoq.Main.Meta_theory.Parallel_postulates",
        "GeoCoq.Constructive.Parallel_postulates" );
      ("GeoCoq.Main.Tactics", "GeoCoq.Constructive.Tactics");
      ("GeoCoq.Axioms.Definitions", "GeoCoq.Constructive.Prelude.Definitions");
      ( "GeoCoq.Axioms.continuity_axioms",
        "GeoCoq.Constructive.Prelude.continuity_axioms" );
      ( "GeoCoq.Axioms.parallel_postulates",
        "GeoCoq.Constructive.Prelude.parallel_postulates" );
    ]
  in
  match x.ast with
  | None -> Ok []
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).v.expr with
      | VernacSynterp
          (VernacRequire
             (option_libname, export_with_cats_opt, libnames_import_list)) -> (
          match libnames_import_list with
          | [] ->
              Error.format_to_or_error
                "Error getting libnames_import_list in %s" (Syntax_node.repr x)
          | (_, _) :: _ -> (
              match
                rewrite_first_import ~rules:require_prefix_rules
                  libnames_import_list
              with
              | None -> Ok []
              | Some new_libnames_import_list ->
                  let* new_node =
                    rebuild_require_node x option_libname export_with_cats_opt
                      new_libnames_import_list
                  in
                  Ok [ Replace (x.id, new_node) ]))
      | _ -> Ok [])

let replace_congr (doc : Rocq_document.t) :
    (transformation_step list, Error.t) result =
  let dummy_start : Code_point.t = { line = 0; character = 0 } in
  if Filename.basename doc.filename = "Ch04_cong_bet.v" then
    Ok
      (List.filter_map
         (fun node ->
           if
             String.equal (Syntax_node.repr node)
               "Ltac congr :=\n\
               \  let tpoint := constr:(Tpoint) in\n\
               \  let cong := constr:(Cong) in\n\
               \    Cong_refl tpoint cong."
           then
             let new_congr =
               Syntax_node.syntax_node_of_string
                 "Ltac congr :=\n\
                 \  let tpoint := constr:(Tpoint) in\n\
                 \  let cong := constr:(CongC) in\n\
                 \    Cong_refl tpoint cong."
                 dummy_start
               |> Result.get_ok
             in
             Some (Replace (node.id, new_congr))
           else None)
         doc.elements)
  else Ok []

let replace_cong_theory (doc : Rocq_document.t) :
    (transformation_step list, Error.t) result =
  let dummy_start : Code_point.t = { line = 0; character = 0 } in
  if Filename.basename doc.filename = "tarski_to_cong_theory.v" then
    Ok
      (List.filter_map
         (fun node ->
           if
             String.equal (Syntax_node.repr node)
               "Global Instance Tarski_is_a_Cong_theory : (Cong_theory Tpoint \
                Cong)."
           then
             let new_global_instance_node =
               Syntax_node.syntax_node_of_string
                 "Global Instance Tarski_is_a_Cong_theory : (Cong_theory \
                  Tpoint CongC)."
                 dummy_start
               |> Result.get_ok
             in
             Some (Replace (node.id, new_global_instance_node))
           else if
             String.equal (Syntax_node.repr node)
               "exact (Build_Cong_theory Tpoint Cong cong_reflexivity \
                cong_left_commutativity cong_symmetry cong_transitivity)."
           then
             let new_exact_node =
               Syntax_node.syntax_node_of_string
                 "exact (Build_Cong_theory Tpoint CongC cong_reflexivity \
                  cong_left_commutativity cong_symmetry cong_transitivity)."
                 dummy_start
               |> Result.get_ok
             in
             Some (Replace (node.id, new_exact_node))
           else None)
         doc.elements)
  else Ok []

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

let attach_prelude_to_file (doc : Rocq_document.t) (filename : string) :
    (transformation_step list, Error.t) result =
  let dummy_start : Code_point.t = { line = 0; character = 0 } in
  if Filename.basename doc.filename = filename then
    let last_require_opt =
      List_utils.find_last_opt Syntax_node.is_syntax_node_require doc.elements
    in
    match last_require_opt with
    | Some last_require ->
        let* prelude_node =
          Syntax_node.syntax_node_of_string
            "Require Export GeoCoq.Constructive.Prelude.Prelude." dummy_start
        in
        Ok [ Attach (prelude_node, LineAfter, last_require.id) ]
    | None ->
        Error.string_to_or_error
          "Attach prelude: No Require node was found, check assumptions !"
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

let replace_decompose_or_with_decompose_stab_or
    (x : Ltac_plugin.Tacexpr.raw_tactic_expr) :
    Ltac_plugin.Tacexpr.raw_tactic_expr =
  match x.v with
  | TacAlias (alias, [ decomposed_args; hypothesis ])
    when String.starts_with
           (Names.KerName.to_string alias)
           ~prefix:"Corelib.Init.Ltac.decompose_[_#_]_#_" -> (
      let decomposed_args_genarg =
        Ltac.get_tac_generic_genarg decomposed_args |> Option.get
      in
      let args_str =
        Raw_gen_args_converter.constr_expr_list_of_raw_generic_argument
          decomposed_args_genarg
        |> Option.map (List.map constrexpr_to_string)
      in
      match args_str with
      | Some [ "or" ] ->
          let hypothesis_genarg =
            Ltac.get_tac_generic_genarg hypothesis |> Option.get
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
            Ltac.get_tac_generic_genarg hypothesis |> Option.get
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

type stab_kind =
  | Inner_pasch
  | Segment_construction
  | Eq_Dec_Points
  | Stab_destruct_with_args
  | Stab_destruct_no_args
  | Stab_elim_no_args

let dummy_tactic_for_kind = function
  | Inner_pasch -> "stab_destruct (by_inner_pasch A B C D X X X) as [I []]."
  | Segment_construction ->
      "stab_destruct (by_segment_construction A B C D) as [I []]."
  | Eq_Dec_Points -> "stab_destruct (by_eq_dec_points B C)."
  | Stab_destruct_no_args -> "stab_destruct H."
  | Stab_destruct_with_args -> "stab_destruct H as [HL|HR]."
  | Stab_elim_no_args -> "stab_elim H."

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

let stab_destruct_with_args_alias_kn : Names.KerName.t option Lazy.t =
  lazy (compute_alias_kername Stab_destruct_with_args)

let stab_destruct_no_args_alias_kn : Names.KerName.t option Lazy.t =
  lazy (compute_alias_kername Stab_destruct_no_args)

let stab_elim_no_args_alias_kn : Names.KerName.t option Lazy.t =
  lazy (compute_alias_kername Stab_elim_no_args)

let get_alias_kn = function
  | Inner_pasch -> Lazy.force inner_pasch_alias_kn
  | Segment_construction -> Lazy.force segment_construction_alias_kn
  | Eq_Dec_Points -> Lazy.force eq_dec_points_alias_kn
  | Stab_destruct_with_args -> Lazy.force stab_destruct_with_args_alias_kn
  | Stab_destruct_no_args -> Lazy.force stab_destruct_no_args_alias_kn
  | Stab_elim_no_args -> Lazy.force stab_elim_no_args_alias_kn

let replace_elim_with_stab_elim (x : Ltac_plugin.Tacexpr.raw_tactic_expr) :
    Ltac_plugin.Tacexpr.raw_tactic_expr =
  match x.v with
  | TacAtom (TacElim (false, binding_args, None)) ->
      (* no eelim (false evar flag + no with *)
      let _, (constrexpr, _) = binding_args in

      let open_constr_arg =
        Raw_gen_args_converter.raw_generic_argument_of_open_constr constrexpr
      in
      let stab_elim_args =
        List.map
          (fun x -> Ltac_plugin.Tacexpr.TacGeneric (None, x))
          [ open_constr_arg ]
      in

      let kername = get_alias_kn Stab_elim_no_args |> Option.get in

      Ltac_plugin.Tacexpr.TacAlias (kername, stab_elim_args) |> CAst.make
  | _ -> x

let constrexpr_to_stab_destruct_fun_name (c : Constrexpr.constr_expr) =
  if is_constrexpr_c_app_named c "inner_pasch" then get_alias_kn Inner_pasch
  else if is_constrexpr_c_app_named c "segment_construction" then
    get_alias_kn Segment_construction
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

              let kername =
                get_alias_kn Stab_destruct_with_args |> Option.get
              in

              let stab_destruct_args =
                List.map
                  (fun x -> Ltac_plugin.Tacexpr.TacGeneric (None, x))
                  [ open_constr_arg; intro_pattern_arg ]
              in

              Ltac_plugin.Tacexpr.TacAlias (kername, stab_destruct_args)
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

              let kername = get_alias_kn Stab_destruct_no_args |> Option.get in

              Ltac_plugin.Tacexpr.TacAlias (kername, stab_destruct_args)
              |> CAst.make
          | _ -> x)
      | ElimOnConstr (constrexpr, NoBindings) -> (
          match constrexpr_to_stab_destruct_fun_name constrexpr with
          | Some kername -> (
              match intro_pattern_naming_expr with
              | _, Some (ArgArg intro_or_and_pattern) ->
                  let fun_args = get_func_args constrexpr in
                  let fun_args_str_opt =
                    List.map
                      (fun x ->
                        get_cref_qualid x
                        |> Option.map Libnames.string_of_qualid)
                      fun_args
                    |> List_utils.option_all
                  in

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
          | None -> (
              match intro_pattern_naming_expr with
              | _, Some (ArgArg intro_or_and_pattern) ->
                  let kername =
                    get_alias_kn Stab_destruct_with_args |> Option.get
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

                  let openconstr_constrexpr =
                    constrexpr
                    |> Raw_gen_args_converter
                       .raw_generic_argument_of_open_constr
                  in

                  let stab_destruct_args =
                    List.map
                      (fun x -> Ltac_plugin.Tacexpr.TacGeneric (None, x))
                      [ openconstr_constrexpr; intro_arg ]
                  in

                  Ltac_plugin.Tacexpr.TacAlias (kername, stab_destruct_args)
                  |> CAst.make
              | _, None ->
                  let kername =
                    get_alias_kn Stab_destruct_no_args |> Option.get
                  in

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
              | _ -> x))
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

let map_raw_tactic_expr_steps
    (f :
      Ltac_plugin.Tacexpr.raw_tactic_expr -> Ltac_plugin.Tacexpr.raw_tactic_expr)
    (doc : Rocq_document.t) : transformation_step list =
  List.filter_map
    (Transformation_utils.map_raw_tactic_expr_in_node f)
    doc.elements

let replace_taccalls_in_tacexpr (renames : (string * string) list)
    (tacexpr : Ltac_plugin.Tacexpr.raw_tactic_expr) :
    Ltac_plugin.Tacexpr.raw_tactic_expr =
  List.fold_left
    (fun expr (old_name, new_name) ->
      Rename.rename_taccall_tacarg_in_tacexpr old_name new_name expr)
    tacexpr renames

let replace_taccalls_steps (renames : (string * string) list)
    (doc : Rocq_document.t) : transformation_step list =
  map_raw_tactic_expr_steps (replace_taccalls_in_tacexpr renames) doc

let constructivise_doc (doc : Rocq_document.t) :
    (transformation_step list, Error.t) result =
  let open Pipeline in
  let token = Coq.Limits.Token.create () in

  let dummy_start : Code_point.t = { line = 0; character = 0 } in

  let* require_prelude_node =
    Syntax_node.syntax_node_of_string
      "Require Import GeoCoq.Constructive.Prelude.Prelude." dummy_start
  in

  let _preload_prelude =
    ignore
      (Runner.get_state_after doc.initial_state token [ require_prelude_node ])
    (* Require Geocoq.Constructive.Stable in the context for syntax_node_of_string ? this is a bit weird but for now, we need to inform Rocq of other export like this, this is not pure at all :[ *)
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
          attach_prelude_to_file doc "Ch02_cong.v"
        in

        let* attach_prelude_to_chapter_twelwe_inted_dec_steps =
          attach_prelude_to_file doc "Ch12_parallel_inter_dec.v"
        in

        let* attach_prelude_to_chapter_13_5_steps =
          attach_prelude_to_file doc "Ch13_5_Pappus_Pascal.v"
        in

        let* attach_prelude_to_project_steps =
          attach_prelude_to_file doc "project.v"
        in

        let* attach_prelude_to_playfair_existential_playfair_steps =
          attach_prelude_to_file doc "playfair_existential_playfair.v"
        in

        let* replace_cong_theory_steps = replace_cong_theory doc in

        let* replace_congr_steps = replace_congr doc in

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
               Transformation_utils.map_definition_body
                 (replace_notation_in_constrexpr old_notation new_notation)
                 x)
               "_ \\/ _" "_ \\_/ _")
            definitions
        in

        Ok
          (List.concat
             [
               prove_decidability_proofs_steps;
               replace_cong_theory_steps;
               replace_congr_steps;
               attach_prelude_to_chapter_two_steps;
               attach_prelude_to_chapter_twelwe_inted_dec_steps;
               attach_prelude_to_chapter_13_5_steps;
               attach_prelude_to_project_steps;
               attach_prelude_to_playfair_existential_playfair_steps;
               replace_require_steps;
               replace_context_steps;
               replace_or_by_constructive_or_in_proofs_steps;
               replace_or_by_constructive_or_in_definitions_steps;
             ]))
  in

  let stage_beeson_ch03 : stage =
    make_stage "stage_beeson_ch03" (fun doc ->
        if String.ends_with ~suffix:"/Ch03_bet.v" doc.filename then
          remove_named_sections [ "Beeson_1"; "Beeson_2" ] doc
        else Ok [])
  in

  (* let stage_1 : stage = *)
  (*   make_stage "stage1" (fun doc -> *)
  (*       let* proofs = Rocq_document.get_proofs doc in *)

  (*       let proofs_with_exists = List.filter is_proof_about_exists proofs in *)

  (*       let* admit_exists_proofs_steps = *)
  (*         List_utils.concat_map_result *)
  (*           (Transformations.admit_and_comment_proof_steps *)
  (*              ~msg:"existential predicate in conclusion" doc) *)
  (*           proofs_with_exists *)
  (*       in *)

  (*       Ok admit_exists_proofs_steps) *)
  (* in *)
  let stage_1 : stage =
    make_stage "rename Bet and Cong in exists" (fun doc ->
        Ok
          (List.filter_map
             (Transformation_utils.map_raw_tactic_expr_in_node
                (Ltac.map_exists_constr_expr replace_bet_and_cong_in_constrexpr))
             doc.elements))
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
            (Transformation_utils.map_definition_body
               replace_bet_and_cong_in_constrexpr)
            definitions_stage_two
        in

        let replace_tactic_calls =
          replace_taccalls_steps
            [
              ("left", "stab_left"); ("right", "stab_right"); ("tauto", "tautoC");
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
            (Transformation_utils.map_raw_tactic_expr_in_node
               (Ltac.map_assert_constr_expr f_assert))
            doc.elements
        in

        Ok replace_bet_by_betc_and_or_by_cons_or_in_assert_steps)
  in

  let stage_4 =
    make_stage "stage4" (fun doc ->
        let replace_induction_by_stab_eq_point_steps =
          map_raw_tactic_expr_steps replace_induction_by_stab_eq_point doc
        in

        let replace_elim_with_stab_elim_steps =
          map_raw_tactic_expr_steps replace_elim_with_stab_elim doc
        in

        Ok
          (List.concat
             [
               replace_induction_by_stab_eq_point_steps;
               replace_elim_with_stab_elim_steps;
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
        let* ltac_nodes = Rocq_document.get_ltac_outside_proofs doc in

        Ok
          (List.filter_map
             (fun x ->
               Transformation_utils.map_tacdef_bodies_in_node Fun.id
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
        (* stage_11; *)
      ]
  in
  Ok (update_replaces steps)
