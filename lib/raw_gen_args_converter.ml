open Sexplib.Sexp
open Ltac_plugin

let raw_tactic_expr_of_raw_generic_argument (arg : Genarg.raw_generic_argument)
    : Tacexpr.raw_tactic_expr option =
  match Serlib.Ser_genarg.sexp_of_raw_generic_argument arg with
  | List
      [
        Atom "GenArg";
        List [ Atom "Rawwit"; List [ Atom "ExtraArg"; Atom "tactic" ] ];
        rems;
      ] ->
      Some (Serlib_ltac.Ser_tacexpr.raw_tactic_expr_of_sexp rems)
  | _ -> None

let raw_generic_argument_of_raw_tactic_expr (tac : Tacexpr.raw_tactic_expr) :
    Genarg.raw_generic_argument =
  let open Sexplib0.Sexp in
  let tac_sexp = Serlib_ltac.Ser_tacexpr.sexp_of_raw_tactic_expr tac in
  let sexp =
    List
      [
        Atom "GenArg";
        List [ Atom "Rawwit"; List [ Atom "ExtraArg"; Atom "tactic" ] ];
        tac_sexp;
      ]
  in
  Serlib.Ser_genarg.raw_generic_argument_of_sexp sexp

let tacdef_body_of_raw_generic_argument (arg : Genarg.raw_generic_argument) :
    Tacexpr.tacdef_body list option =
  match Serlib.Ser_genarg.sexp_of_raw_generic_argument arg with
  | List
      [
        Atom "GenArg";
        List
          [
            Atom "Rawwit";
            List
              [
                Atom "ListArg";
                List [ Atom "ExtraArg"; Atom "ltac_tacdef_body" ];
              ];
          ];
        List rems;
      ] ->
      Some (List.map Serlib_ltac.Ser_tacexpr.tacdef_body_of_sexp rems)
  | _ -> None

let constr_expr_of_raw_generic_argument (arg : Genarg.raw_generic_argument) :
    Constrexpr.constr_expr option =
  match Serlib.Ser_genarg.sexp_of_raw_generic_argument arg with
  | List
      [
        Atom "GenArg";
        List [ Atom "Rawwit"; List [ Atom "ExtraArg"; Atom "constr" ] ];
        rems;
      ]
  | List
      [
        Atom "GenArg";
        List [ Atom "Rawwit"; List [ Atom "ExtraArg"; Atom "uconstr" ] ];
        rems;
      ] ->
      Some (Serlib.Ser_constrexpr.constr_expr_of_sexp rems)
  | _ -> None

let intro_pattern_list_of_raw_generic_argument
    (arg : Genarg.raw_generic_argument) : Tacexpr.intro_pattern list option =
  match Serlib.Ser_genarg.sexp_of_raw_generic_argument arg with
  | List
      [
        Atom "GenArg";
        List
          [
            Atom "Rawwit";
            List
              [
                Atom "ListArg";
                List [ Atom "ExtraArg"; Atom "simple_intropattern" ];
              ];
          ];
        List rems;
      ] ->
      Some (List.map Serlib_ltac.Ser_tacexpr.intro_pattern_of_sexp rems)
  | _ -> None

let intro_pattern_of_raw_generic_argument (arg : Genarg.raw_generic_argument) :
    Tacexpr.intro_pattern option =
  match Serlib.Ser_genarg.sexp_of_raw_generic_argument arg with
  | List
      [
        Atom "GenArg";
        List
          [
            Atom "Rawwit"; List [ Atom "ExtraArg"; Atom "simple_intropattern" ];
          ];
        rems;
      ] ->
      Some (Serlib_ltac.Ser_tacexpr.intro_pattern_of_sexp rems)
  | _ -> None

let destruction_arg_of_raw_generic_argument (arg : Genarg.raw_generic_argument)
    :
    (Constrexpr.constr_expr * 'a Tactypes.bindings)
    Serlib.Ser_tactics.destruction_arg
    option =
  let open Sexplib.Sexp in
  match Serlib.Ser_genarg.sexp_of_raw_generic_argument arg with
  | List
      [
        Atom "GenArg";
        List [ Atom "Rawwit"; List [ Atom "ExtraArg"; Atom "destruction_arg" ] ];
        rems;
      ] ->
      let arg_parser = function
        | List [ _; expr ] ->
            (Serlib.Ser_constrexpr.constr_expr_of_sexp expr, Tactypes.NoBindings)
        | _ -> failwith "TODO"
      in
      Some (Serlib.Ser_tactics.destruction_arg_of_sexp arg_parser rems)
  | _ -> None

let clause_expr_of_raw_generic_argument (arg : Genarg.raw_generic_argument) :
    Tacexpr.t_nam CAst.t Locus.clause_expr option =
  let open Sexplib.Sexp in
  match Serlib.Ser_genarg.sexp_of_raw_generic_argument arg with
  | List
      [
        Atom "GenArg";
        List [ Atom "Rawwit"; List [ Atom "ExtraArg"; Atom "in_clause" ] ];
        rems;
      ] ->
      Some
        (Serlib.Ser_locus.clause_expr_of_sexp
           (Serlib.Ser_cAst.t_of_sexp Serlib.Ser_names.Id.t_of_sexp)
           rems)
  | _ -> None

let bindings_list_of_raw_generic_argument (arg : Genarg.raw_generic_argument) :
    Constrexpr.constr_expr Tactypes.bindings list option =
  match Serlib.Ser_genarg.sexp_of_raw_generic_argument arg with
  | List
      [
        Atom "GenArg";
        List
          [
            Atom "Rawwit";
            List [ Atom "ListArg"; List [ Atom "ExtraArg"; Atom "bindings" ] ];
          ];
        List rems;
      ] ->
      Some
        (List.map
           (Serlib.Ser_tactypes.bindings_of_sexp
              Serlib.Ser_constrexpr.constr_expr_of_sexp)
           rems)
  | _ -> None

let id_of_raw_generic_argument (arg : Genarg.raw_generic_argument) :
    Tacexpr.t_nam option =
  match Serlib.Ser_genarg.sexp_of_raw_generic_argument arg with
  | List
      [
        Atom "GenArg";
        List [ Atom "Rawwit"; List [ Atom "ExtraArg"; Atom "ident" ] ];
        rems;
      ] ->
      Some (Serlib.Ser_names.Id.t_of_sexp rems)
  | _ -> None

let hyp_list_of_raw_generic_argument (arg : Genarg.raw_generic_argument) :
    Tacexpr.t_nam CAst.t list option =
  match Serlib.Ser_genarg.sexp_of_raw_generic_argument arg with
  | List
      [
        Atom "GenArg";
        List
          [
            Atom "Rawwit";
            List [ Atom "ListArg"; List [ Atom "ExtraArg"; Atom "hyp" ] ];
          ];
        List rems;
      ] ->
      Some
        (List.map
           (Serlib.Ser_cAst.t_of_sexp Serlib.Ser_names.Id.t_of_sexp)
           rems)
  | _ -> None

let hyp_of_raw_generic_argument (arg : Genarg.raw_generic_argument) :
    Tacexpr.t_nam CAst.t option =
  match Serlib.Ser_genarg.sexp_of_raw_generic_argument arg with
  | List
      [
        Atom "GenArg";
        List [ Atom "Rawwit"; List [ Atom "ExtraArg"; Atom "hyp" ] ];
        rems;
      ] ->
      Some (Serlib.Ser_cAst.t_of_sexp Serlib.Ser_names.Id.t_of_sexp rems)
  | _ -> None

let nat_or_var_of_raw_generic_argument (arg : Genarg.raw_generic_argument) :
    int Locus.or_var list option =
  match Serlib.Ser_genarg.sexp_of_raw_generic_argument arg with
  | List
      [
        Atom "GenArg";
        List
          [
            Atom "Rawwit";
            List [ Atom "OptArg"; List [ Atom "ExtraArg"; Atom "nat_or_var" ] ];
          ];
        List rems;
      ] ->
      Some
        (List.map
           (Serlib.Ser_locus.or_var_of_sexp Sexplib.Std.int_of_sexp)
           rems)
  | _ -> None

let auto_using_of_raw_generic_argument (arg : Genarg.raw_generic_argument) :
    Constrexpr.constr_expr list option =
  match Serlib.Ser_genarg.sexp_of_raw_generic_argument arg with
  | List
      [
        Atom "GenArg";
        List [ Atom "Rawwit"; List [ Atom "ExtraArg"; Atom "auto_using" ] ];
        List rems;
      ] ->
      Some (List.map Serlib.Ser_constrexpr.constr_expr_of_sexp rems)
  | _ -> None

let ltac_use_default_of_raw_generic_argument (arg : Genarg.raw_generic_argument)
    : bool option =
  match Serlib.Ser_genarg.sexp_of_raw_generic_argument arg with
  | List
      [
        Atom "GenArg";
        List
          [ Atom "Rawwit"; List [ Atom "ExtraArg"; Atom "ltac_use_default" ] ];
        rems;
      ] ->
      Some (Sexplib.Std.bool_of_sexp rems)
  | _ -> None

let ltac_of_raw_generic_argument (arg : Genarg.raw_generic_argument) :
    Tacexpr.raw_tactic_expr option =
  match Serlib.Ser_genarg.sexp_of_raw_generic_argument arg with
  | List
      [
        Atom "GenArg";
        List [ Atom "Rawwit"; List [ Atom "ExtraArg"; Atom "ltac" ] ];
        rems;
      ] ->
      Some (Serlib_ltac.Ser_tacexpr.raw_tactic_expr_of_sexp rems)
  | _ -> None

let hintbases_of_raw_generic_argument (arg : Genarg.raw_generic_argument) :
    string list option =
  match Serlib.Ser_genarg.sexp_of_raw_generic_argument arg with
  | List
      [
        Atom "GenArg";
        List [ Atom "Rawwit"; List [ Atom "ExtraArg"; Atom "hintbases" ] ];
        List [ List rems ];
      ] ->
      Some (List.map Sexplib.Std.string_of_sexp rems)
  | _ -> None

let string_of_raw_generic_argument (arg : Genarg.raw_generic_argument) :
    string option =
  match Serlib.Ser_genarg.sexp_of_raw_generic_argument arg with
  | List
      [
        Atom "GenArg";
        List [ Atom "Rawwit"; List [ Atom "ExtraArg"; Atom "string" ] ];
        rems;
      ] ->
      Some (Sexplib.Std.string_of_sexp rems)
  | _ -> None

let ref_of_raw_generic_argument (arg : Genarg.raw_generic_argument) :
    Libnames.qualid option =
  match Serlib.Ser_genarg.sexp_of_raw_generic_argument arg with
  | List
      [
        Atom "GenArg";
        List [ Atom "Rawwit"; List [ Atom "ExtraArg"; Atom "ref" ] ];
        rems;
      ] ->
      Some (Serlib.Ser_libnames.qualid_of_sexp rems)
  | _ -> None

let ref_list_of_raw_generic_argument (arg : Genarg.raw_generic_argument) :
    Libnames.qualid list option =
  match Serlib.Ser_genarg.sexp_of_raw_generic_argument arg with
  | List
      [
        Atom "GenArg";
        List
          [
            Atom "Rawwit";
            List [ Atom "ListArg"; List [ Atom "ExtraArg"; Atom "ref" ] ];
          ];
        List rems;
      ] ->
      Some (List.map Serlib.Ser_libnames.qualid_of_sexp rems)
  | _ -> None

let opt_string_of_raw_generic_argument (arg : Genarg.raw_generic_argument) :
    string option option =
  match Serlib.Ser_genarg.sexp_of_raw_generic_argument arg with
  | List
      [
        Atom "GenArg";
        List
          [
            Atom "Rawwit";
            List [ Atom "OptArg"; List [ Atom "ExtraArg"; Atom "string" ] ];
          ];
        rems;
      ] ->
      Some (Sexplib.Std.option_of_sexp Sexplib.Std.string_of_sexp rems)
  | _ -> None

let by_arg_tac_of_raw_generic_argument (arg : Genarg.raw_generic_argument) :
    Tacexpr.raw_tactic_expr list option =
  match Serlib.Ser_genarg.sexp_of_raw_generic_argument arg with
  | List
      [
        Atom "GenArg";
        List [ Atom "Rawwit"; List [ Atom "ExtraArg"; Atom "by_arg_tac" ] ];
        List rems;
      ] ->
      Some (List.map Serlib_ltac.Ser_tacexpr.raw_tactic_expr_of_sexp rems)
  | _ -> None

let clause_dft_concl_of_raw_generic_argument (arg : Genarg.raw_generic_argument)
    : Tacexpr.t_nam CAst.t Locus.clause_expr option =
  match Serlib.Ser_genarg.sexp_of_raw_generic_argument arg with
  | List
      [
        Atom "GenArg";
        List
          [ Atom "Rawwit"; List [ Atom "ExtraArg"; Atom "clause_dft_concl" ] ];
        rems;
      ] ->
      Some
        (Serlib.Ser_locus.clause_expr_of_sexp
           (Serlib.Ser_cAst.t_of_sexp Serlib.Ser_names.Id.t_of_sexp)
           rems)
  | _ -> None

let constr_with_bindings_of_raw_generic_argument
    (arg : Genarg.raw_generic_argument) :
    Constrexpr.constr_expr Serlib.Ser_tactypes.with_bindings option =
  match Serlib.Ser_genarg.sexp_of_raw_generic_argument arg with
  | List
      [
        Atom "GenArg";
        List
          [
            Atom "Rawwit"; List [ Atom "ExtraArg"; Atom "constr_with_bindings" ];
          ];
        rems;
      ] ->
      Some
        (Serlib.Ser_tactypes.with_bindings_of_sexp
           Serlib.Ser_constrexpr.constr_expr_of_sexp rems)
  | _ -> None

let rename_idents_of_raw_generic_argument (arg : Genarg.raw_generic_argument) :
    (Tacexpr.t_nam * Tacexpr.t_nam) list option =
  match Serlib.Ser_genarg.sexp_of_raw_generic_argument arg with
  | List
      [
        Atom "GenArg";
        List
          [
            Atom "Rawwit";
            List [ Atom "ListArg"; List [ Atom "ExtraArg"; Atom "rename" ] ];
          ];
        List rems;
      ] ->
      Some
        (List.map
           (Sexplib.Conv.pair_of_sexp Serlib.Ser_names.Id.t_of_sexp
              Serlib.Ser_names.Id.t_of_sexp)
           rems)
  | _ -> None

let ltac_production_item_of_raw_generic_argument
    (arg : Genarg.raw_generic_argument) :
    unit Pptactic.grammar_tactic_prod_item_expr list option =
  match Serlib.Ser_genarg.sexp_of_raw_generic_argument arg with
  | List
      [
        Atom "GenArg";
        List
          [
            Atom "Rawwit";
            List
              [
                Atom "ListArg";
                List [ Atom "ExtraArg"; Atom "ltac_production_item" ];
              ];
          ];
        List rems;
      ] ->
      Some
        (List.map
           (Serlib_ltac.Ser_tacentries.grammar_tactic_prod_item_expr_of_sexp
              (fun _ -> (* TODO *) ()))
           rems)
  | _ -> None

let ltac_tactic_level_of_raw_generic_argument
    (arg : Genarg.raw_generic_argument) : int option option =
  match Serlib.Ser_genarg.sexp_of_raw_generic_argument arg with
  | List
      [
        Atom "GenArg";
        List [ Atom "Rawwit"; List [ Atom "OptArg"; Atom "ltac_tactic_level" ] ];
        rems;
      ] ->
      Some (Sexplib.Std.option_of_sexp Sexplib.Std.int_of_sexp rems)
  | _ -> None

let test_lpar_id_colon_of_raw_generic_argument
    (arg : Genarg.raw_generic_argument) =
  match Serlib.Ser_genarg.sexp_of_raw_generic_argument arg with
  | List
      [
        Atom "GenArg";
        List
          [ Atom "Rawwit"; List [ Atom "ExtraArg"; Atom "test_lpar_id_colon" ] ];
        rems;
      ] ->
      Some (Sexplib.Std.unit_of_sexp rems)
  | _ -> None

let lconstr_of_raw_generic_argument (arg : Genarg.raw_generic_argument) :
    Constrexpr.constr_expr option =
  match Serlib.Ser_genarg.sexp_of_raw_generic_argument arg with
  | List
      [
        Atom "GenArg";
        List [ Atom "Rawwit"; List [ Atom "ExtraArg"; Atom "lconstr" ] ];
        rems;
      ] ->
      Some (Serlib.Ser_constrexpr.constr_expr_of_sexp rems)
  | _ -> None

let ltac_selector_of_raw_generic_argument (arg : Genarg.raw_generic_argument) :
    Goal_select.t option option =
  match Serlib.Ser_genarg.sexp_of_raw_generic_argument arg with
  | List
      [
        Atom "GenArg";
        List
          [
            Atom "Rawwit";
            List
              [ Atom "OptArg"; List [ Atom "ExtraArg"; Atom "ltac_selector" ] ];
          ];
        rems;
      ] ->
      Some (Sexplib.Std.option_of_sexp Serlib.Ser_goal_select.t_of_sexp rems)
  | _ -> None

type ltac_elements = {
  selector : Goal_select.t option;
  raw_tactic_expr : Ltac_plugin.Tacexpr.raw_tactic_expr;
  use_default : bool; (* TODO parse last args *)
}

let raw_arguments_to_ltac_elements (args : Genarg.raw_generic_argument list) :
    ltac_elements option =
  if List.length args != 4 then None
  else
    let first_arg = List.nth args 0 in
    let _ = List.nth args 1 in
    let third_arg = List.nth args 2 in
    let fourth_arg = List.nth args 3 in
    let selector =
      Option.get (ltac_selector_of_raw_generic_argument first_arg)
    in
    (* TODO parse second arg *)
    let raw_tactic_expr =
      Option.get (raw_tactic_expr_of_raw_generic_argument third_arg)
    in
    let use_default =
      Option.get (ltac_use_default_of_raw_generic_argument fourth_arg)
    in
    Some { selector; raw_tactic_expr; use_default }

let raw_arguments_to_raw_tactic_expr (args : Genarg.raw_generic_argument list) :
    Ltac_plugin.Tacexpr.raw_tactic_expr option =
  match args with
  | [ _; _; arg; _ ] -> raw_tactic_expr_of_raw_generic_argument arg
  | _ -> None
