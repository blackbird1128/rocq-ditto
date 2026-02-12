open Proof
open Vernacexpr
open Constructivisation_data

let ( let* ) = Result.bind
let ( let+ ) = Option.bind

module Syntax_nodeSet = Set.Make (struct
  type t = Syntax_node.t

  let compare = Syntax_node.compare
end)

let show_list xs = "[" ^ String.concat "; " xs ^ "]"

(* this is N^2 but we don't really care as the lists are quite small *)
let intersect l1 l2 = List.exists (fun x -> List.mem x l1) l2

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
          | Some (qualid, import_filter) ->
              let qualid_str = Libnames.string_of_qualid qualid in
              if String.starts_with ~prefix:"GeoCoq.Main.Tarski_dev" qualid_str
              then
                let _, postfix =
                  split_prefix "GeoCoq.Main.Tarski_dev" qualid_str |> Option.get
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

let attach_prelude_to_chapter_two (doc : Rocq_document.t) :
    (transformation_step list, Error.t) result =
  let dummy_start : Code_point.t = { line = 0; character = 0 } in
  if Filename.basename doc.filename = "Ch02_cong.v" then
    let last_require =
      List.find Syntax_node.is_syntax_node_require (List.rev doc.elements)
    in
    let* prelude_node =
      Syntax_node.syntax_node_of_string
        "Require Export GeoCoq.Constructive.Prelude." dummy_start
    in
    Ok [ Attach (prelude_node, LineAfter, last_require.id) ]
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

let get_fun_name_in_constrexpr (term : Constrexpr.constr_expr) :
    Libnames.qualid option =
  match term.v with
  | Constrexpr.CRef (q, _) -> Some q
  | Constrexpr.CAppExpl ((q, _), _) -> Some q
  | _ -> None

let get_fun_names_in_constrexpr (term : Constrexpr.constr_expr) :
    Libnames.qualid list =
  Constrexpr_fold.fold
    (fun x acc ->
      match get_fun_name_in_constrexpr x with
      | Some qualid -> qualid :: acc
      | None -> acc)
    [] term

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
      let call_qualid, fun_args = call_arg.v in
      if String.equal (Libnames.string_of_qualid call_qualid) "prolong" then
        let args_str_opt = List.map prolong_arg_to_string fun_args in
        match List_utils.option_all args_str_opt with
        | Some [ args0; args1; args2; args3; args4 ] -> (
            let segment_construction_str =
              Printf.sprintf
                "apply (by_segment_construction %s %s %s %s); [solve_stable | \
                 intros [%s [?H ?H]]]."
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

let map_raw_tactic_expr_in_node
    (f :
      Ltac_plugin.Tacexpr.raw_tactic_expr -> Ltac_plugin.Tacexpr.raw_tactic_expr)
    (node : Syntax_node.t) : transformation_step option =
  let+ raw_tac_expr = Syntax_node.get_node_raw_tactic_expr node in
  let raw_expr_mapped = Tacexpr_map.tacexpr_map f raw_tac_expr in
  if raw_tac_expr = raw_expr_mapped then None
  else
    let selector = Syntax_node.get_node_goal_selector_opt node in
    let+ new_node =
      Syntax_node.raw_tactic_expr_to_syntax_node raw_expr_mapped ?selector
        node.range.start
      |> Result.to_option
    in
    Some (Replace (node.id, new_node))

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

let is_constrexpr_c_app_named (x : Constrexpr.constr_expr) (name : string) :
    bool =
  match x.v with
  | Constrexpr.CApp (func, _) ->
      Option.map Libnames.string_of_qualid (get_cref_qualid func) = Some name
  | _ -> false

let get_func_args (x : Constrexpr.constr_expr) : Constrexpr.constr_expr list =
  match x.v with Constrexpr.CApp (_, args) -> List.map fst args | _ -> []

let get_tac_generic_genarg
    (x : Ltac_plugin.Tacexpr.r_dispatch Ltac_plugin.Tacexpr.gen_tactic_arg) =
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
        |> Option.get
        |> List.map constrexpr_to_string
      in
      match args_str with
      | [ "or" ] ->
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
      | [ "or"; "and" ] | [ "and"; "or" ] ->
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
              "stab_eq_point " ^ String.concat " " fun_args_str ^ "."
            in

            match Syntax_node.string_to_raw_tactic_expr stab_eq_str with
            | Ok expr -> expr
            | Error _ -> x)
        | None -> x
      else x
  | _ -> x

let constrexpr_to_stab_destruct_fun_name (c : Constrexpr.constr_expr) :
    string option =
  if is_constrexpr_c_app_named c "inner_pasch" then
    Some "stab_destruct_(_inner_pasch_#_#_#_#_#_#_#_)_as_#_0A64625C"
  else if is_constrexpr_c_app_named c "segment_construction" then
    Some "stab_destruct_(_segment_construction_#_#_#_#_)_as_#_0A64625D"
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
      | ElimOnConstr (constrexpr, NoBindings) -> (
          match constrexpr_to_stab_destruct_fun_name constrexpr with
          | Some kername_label -> (
              let fun_args = get_func_args constrexpr in
              let fun_args_str_opt =
                List.map
                  (fun x ->
                    get_cref_qualid x |> Option.map Libnames.string_of_qualid)
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
              match intro_pattern_naming_expr with
              | _, Some (ArgArg intro_or_and_pattern) ->
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

                  let kername_modules : Names.Id.t list =
                    [
                      Names.Id.of_string "Prelude";
                      Names.Id.of_string "Constructive";
                      Names.Id.of_string "GeoCoq";
                    ]
                  in
                  let ker_name_dir_path : Names.DirPath.t =
                    Names.DirPath.make kername_modules
                  in
                  let ker_name_modpath : Names.ModPath.t =
                    MPfile ker_name_dir_path
                  in
                  let stab_destruct_str_label =
                    Names.Label.of_id (Names.Id.of_string_soft kername_label)
                  in

                  let ker_name =
                    Names.KerName.make ker_name_modpath stab_destruct_str_label
                  in

                  let stab_destruct_args =
                    List.map
                      (fun x -> Ltac_plugin.Tacexpr.TacGeneric (None, x))
                      (fun_args_name_id_arg @ [ intro_arg ])
                  in

                  Ltac_plugin.Tacexpr.TacAlias (ker_name, stab_destruct_args)
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

let replace_notation_in_definition (old_notation : string)
    (new_notation : string) (x : Syntax_node.t) : transformation_step option =
  map_definition_body
    (replace_notation_in_constrexpr old_notation new_notation)
    x

let add_node_after_require (doc : Rocq_document.t) (node : Syntax_node.t) :
    transformation_step option =
  match
    List_utils.find_last_opt Syntax_node.is_syntax_node_require doc.elements
  with
  | Some last_require -> Some (Attach (node, LineAfter, last_require.id))
  | None -> None

let constrexpr_contains_exists (x : Constrexpr.constr_expr) : bool =
  Constrexpr_fold.exists
    (fun expr ->
      match expr.v with
      | Constrexpr.CNotation (_, (_, notation_key), _) ->
          notation_key = "exists _ .. _ , _"
      | _ -> false)
    x

module StringSet = Set.Make (String)

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

let get_proof_conclusion (p : Proof.t) : Constrexpr.constr_expr option =
  let ( let+ ) = Option.bind in
  let+ components = Proof.get_theorem_components p in
  let expr = components.expr in
  let rec get_conclusion (expr : Constrexpr.constr_expr) =
    match expr.v with
    | Constrexpr.CProdN (_, body) -> get_conclusion body
    | Constrexpr.CLetIn (_, _, _, body) -> get_conclusion body
    | Constrexpr.CNotation (_, (_, notation_key), (args, _, _, _)) ->
        if notation_key = "_ -> _" then (
          match args with
          | [ _; right ] -> get_conclusion right
          | _ ->
              Logs.debug (fun m -> m "this is NOT supposed to happens");
              None)
        else Some expr
    | _ -> Some expr
  in
  get_conclusion expr

let get_syntax_node_assert_expr (x : Syntax_node.t) :
    Constrexpr.constr_expr option =
  match Syntax_node.get_node_raw_atomic_tactic_expr x with
  | Some (TacAssert (false, true, _, _, expr)) -> Some expr
  | _ -> None

let is_proof_about_exists (p : Proof.t) : bool =
  match get_proof_conclusion p with
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

let remove_decidability_proofs (doc : Rocq_document.t) :
    (transformation_step list, Error.t) result =
  let* proofs = Rocq_document.get_proofs doc in
  let decidability_proofs =
    List.filter
      (fun p ->
        let name = Proof.get_proof_name p in
        List.exists
          (fun x -> Option.equal String.equal name (Some x))
          decidability_lemmas)
      proofs
  in
  Ok
    (List.concat_map
       (fun p ->
         let nodes = Proof.proof_nodes p in
         List.map (fun (node : Syntax_node.t) -> Remove node.id) nodes)
       decidability_proofs)

let check_definitions_containing_exists_are_correct (doc : Rocq_document.t)
    (static_definitions : string list) : (unit, Error.t) result =
  if Filename.basename doc.filename = "Definitions.v" then
    let definitions =
      List.filter Syntax_node.is_syntax_node_definition doc.elements
    in

    let definitions_containing_exists =
      collect_definitions_containing_exists definitions
    in

    if List.equal String.equal definitions_containing_exists static_definitions
    then Ok ()
    else
      Error.string_to_or_error
        "Mismatch between the statically defined definitions containing exists \
         and the dynamically collected ones"
  else Ok ()

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

let definitions_of (d : Rocq_document.t) : Syntax_node.t list =
  List.filter Syntax_node.is_syntax_node_definition d.elements

type stage = {
  name : string;
  build_steps : Rocq_document.t -> (transformation_step list, Error.t) result;
}

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

let constructivize_doc (doc : Rocq_document.t) :
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

  (* stage 0 *)
  let* _ =
    check_definitions_containing_exists_are_correct doc definitions_with_exists
  in

  let stage_0 : stage =
    {
      name = "stage0";
      build_steps =
        (fun doc ->
          let* proofs = Rocq_document.get_proofs doc in

          let decidability_proofs : Proof.t list =
            List.filter
              (fun p ->
                let name = Proof.get_proof_name p in
                List.exists
                  (fun x -> Option.equal String.equal name (Some x))
                  decidability_lemmas)
              proofs
          in

          let* admit_decidability_proofs_steps =
            List_utils.concat_map_result
              (Transformations.admit_and_comment_proof_steps doc)
              decidability_proofs
          in

          let* attach_prelude_to_chapter_two_steps =
            attach_prelude_to_chapter_two doc
          in

          let* replace_require_steps =
            List_utils.concat_map_result replace_require doc.elements
          in

          let* replace_context_steps =
            List_utils.concat_map_result replace_context doc.elements
          in

          let definitions = definitions_of doc in

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

          Ok
            (List.concat
               [
                 admit_decidability_proofs_steps;
                 attach_prelude_to_chapter_two_steps;
                 replace_require_steps;
                 replace_context_steps;
                 replace_or_by_constructive_or_in_proofs_steps;
                 replace_or_by_constructive_or_in_definitions_steps;
               ]));
    }
  in
  (***** end of stage 1 **************)

  let decompose_or_and_raw_expr =
    Syntax_node.string_to_raw_tactic_expr "decompose [or and] H."
    |> Result.get_ok
  in
  let decompose_or_and_sexp =
    Serlib_ltac.Ser_tacexpr.sexp_of_raw_tactic_expr decompose_or_and_raw_expr
  in
  Logs.debug (fun m ->
      m "decompose or and sexp: %s"
        (Sexplib.Sexp.to_string_hum decompose_or_and_sexp));

  let stage_1 : stage =
    {
      name = "stage1";
      build_steps =
        (fun doc ->
          let* proofs = Rocq_document.get_proofs doc in

          let proofs_with_exists = List.filter is_proof_about_exists proofs in

          let* admit_exists_proofs_steps =
            List_utils.concat_map_result
              (Transformations.admit_and_comment_proof_steps doc)
              proofs_with_exists
          in

          Ok admit_exists_proofs_steps);
    }
  in

  let stage_2 : stage =
    {
      name = "stage2";
      build_steps =
        (fun doc ->
          let* proofs_stage_two = Rocq_document.get_proofs doc in

          let definitions_stage_two = definitions_of doc in

          let constructivise_bet_and_cong_f =
            Fun.compose
              (replace_fun_name_in_constrexpr "Bet" "BetC")
              (replace_fun_name_in_constrexpr "Cong" "CongC")
          in

          let replace_bet_and_cong_by_cons_ver_in_proofs_steps =
            List.filter_map
              (map_proof_proposition constructivise_bet_and_cong_f)
              proofs_stage_two
          in

          let replace_bet_and_cong_by_cons_ver_definitions_steps =
            List.filter_map
              (map_definition_body constructivise_bet_and_cong_f)
              definitions_stage_two
          in

          let replace_left_by_stab_left =
            List.filter_map
              (replace_taccall_tacarg_in_node "left" "stab_left")
              doc.elements
          in

          Ok
            (List.concat
               [
                 replace_bet_and_cong_by_cons_ver_in_proofs_steps;
                 replace_bet_and_cong_by_cons_ver_definitions_steps;
                 replace_left_by_stab_left;
               ]));
    }
  in

  let stage_3 =
    {
      name = "stage3";
      build_steps =
        (fun doc ->
          let replace_right_by_stab_right =
            List.filter_map
              (replace_taccall_tacarg_in_node "right" "stab_right")
              doc.elements
          in
          Ok replace_right_by_stab_right);
    }
  in

  let stage_4 =
    {
      name = "stage4";
      build_steps =
        (fun doc ->
          let f_assert =
           fun x ->
            replace_fun_name_in_constrexpr "Bet" "BetC" x
            |> replace_fun_name_in_constrexpr "Cong" "CongC"
            |> replace_notation_in_constrexpr "_ \\/ _" "_ \\_/ _"
          in

          let replace_bet_by_betc_and_or_by_cons_or_in_assert_steps =
            List.filter_map (map_assert_in_node f_assert) doc.elements
          in

          Ok replace_bet_by_betc_and_or_by_cons_or_in_assert_steps);
    }
  in

  let stage_5 =
    {
      name = "stage5";
      build_steps =
        (fun doc ->
          let replace_induction_by_stab_eq_point_steps =
            List.filter_map
              (map_raw_tactic_expr_in_node replace_induction_by_stab_eq_point)
              doc.elements
          in

          let replace_elim_with_stab_eq_point_steps =
            List.filter_map
              (map_raw_tactic_expr_in_node replace_elim_with_stab_eq_point)
              doc.elements
          in

          Ok
            (List.concat
               [
                 replace_induction_by_stab_eq_point_steps;
                 replace_elim_with_stab_eq_point_steps;
               ]));
    }
  in

  let stage_6 : stage =
    {
      name = "stage6";
      build_steps =
        (fun doc ->
          let prolong_to_segment_cons_steps =
            List.filter_map
              (map_raw_tactic_expr_in_node replace_prolong_by_segment_cons)
              doc.elements
          in

          Ok prolong_to_segment_cons_steps);
    }
  in

  let stage_7 : stage =
    {
      name = "stage7";
      build_steps =
        (fun doc ->
          let decompose_or_to_stab_version_steps =
            List.filter_map
              (map_raw_tactic_expr_in_node
                 replace_decompose_or_with_decompose_stab_or)
              doc.elements
          in

          Ok decompose_or_to_stab_version_steps);
    }
  in

  let stage_8 : stage =
    {
      name = "stage8";
      build_steps =
        (fun doc ->
          let steps =
            List.filter_map
              (map_raw_tactic_expr_in_node
                 replace_destruct_fun_with_stab_destruct)
              doc.elements
          in
          Ok steps);
    }
  in

  let stage_9 : stage =
    {
      name = "stage9";
      build_steps =
        (fun doc ->
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

          let f_tacdef_constr =
            Fun.compose
              (replace_fun_name_in_constrexpr "Bet" "BetC")
              (replace_fun_name_in_constrexpr "Cong" "CongC")
          in

          Ok
            (List.filter_map
               (fun x ->
                 map_tacdef_bodies_in_node Fun.id
                   (Constrexpr_map.constr_expr_map f_tacdef_constr)
                   x)
               ltac_nodes));
    }
  in

  (* let stage_10 :  stage = { *)
  (*     name = "stage10"; *)
  (*     build_steps = (fun doc -> ) *)

  (*   } *)
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
        stage_1;
        stage_2;
        stage_3;
        stage_4;
        stage_5;
        stage_6;
        stage_7;
        stage_8;
        stage_9;
        (* stage_11; *)
      ]
  in
  Ok (update_replaces steps)
