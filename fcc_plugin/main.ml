open Fleche
open Ditto
open Ditto.Proof_tree
open Ditto.Proof
open Ditto.Syntax_node
open Vernacexpr
open Theorem_query

type transformation_kind =
  | Help
  | MakeIntrosExplicit
  | TurnIntoOneliner
  | ReplaceAutoWithSteps
  | CompressIntro
  | IdTransformation

let transformation_kind_to_arg (kind : transformation_kind) : string =
  match kind with
  | Help -> "HELP"
  | MakeIntrosExplicit -> "MAKE_INTROS_EXPLICIT"
  | TurnIntoOneliner -> "TURN_INTO_ONELINER"
  | ReplaceAutoWithSteps -> "REPLACE_AUTO_WITH_STEPS"
  | CompressIntro -> "COMPRESS_INTROS"
  | IdTransformation -> "ID_TRANSFORMATION"

let arg_to_transformation_kind (arg : string) :
    (transformation_kind, string) result =
  let normalized = String.lowercase_ascii arg in
  if normalized = "help" then Ok Help
  else if normalized = "make_intros_explicit" then Ok MakeIntrosExplicit
  else if normalized = "turn_into_one_liner" then Ok TurnIntoOneliner
  else if normalized = "replace_auto_with_steps" then Ok ReplaceAutoWithSteps
  else if normalized = "compress_intro" then Ok CompressIntro
  else if normalized = "id_transformation" then Ok IdTransformation
  else
    Error
      ("transformation " ^ arg ^ "wasn't recognized as a valid transformation")

let wrap_to_treeify doc x = Result.get_ok (Runner.treeify_proof doc x)

let transformation_kind_to_function (doc : Coq_document.t)
    (kind : transformation_kind) :
    Coq_document.t -> Proof.proof -> (transformation_step list, string) result =
  match kind with
  | Help -> fun doc x -> Ok []
  | MakeIntrosExplicit -> Transformations.make_intros_explicit
  | TurnIntoOneliner ->
      fun doc x ->
        Transformations.turn_into_oneliner doc (wrap_to_treeify doc x)
  | ReplaceAutoWithSteps -> Transformations.replace_auto_with_steps
  | CompressIntro -> Transformations.compress_intro
  | IdTransformation -> Transformations.id_transform

let print_help (transformation_help : (transformation_kind * string) list) :
    unit =
  List.iter
    (fun (kind, help) ->
      print_endline (transformation_kind_to_arg kind ^ ": " ^ help);
      print_newline ())
    transformation_help

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

let rec replace_func (new_func_name : Constrexpr.constr_expr)
    (term : Constrexpr.constr_expr) : Constrexpr.constr_expr =
  match term.v with
  | Constrexpr.CRef (qualid, instance_expr) -> term (* terminal ? *)
  | Constrexpr.CFix (_, _) -> term
  | Constrexpr.CCoFix (_, _) -> term
  | Constrexpr.CProdN (binders, expr) -> replace_func new_func_name expr
  | Constrexpr.CLambdaN (binders, expr) -> replace_func new_func_name expr
  | Constrexpr.CLetIn (name, expr, expr_opt, expr_bis) ->
      CAst.make
        (Constrexpr.CLetIn
           ( name,
             replace_func new_func_name expr,
             Option.map (replace_func new_func_name) expr_opt,
             replace_func new_func_name expr_bis ))
  | Constrexpr.CAppExpl (_, _) -> term
  | Constrexpr.CApp (f, args) ->
      CAst.make (Constrexpr.CApp (new_func_name, args))
  | Constrexpr.CProj (_, _, _, _) -> term
  | Constrexpr.CRecord list -> term
  | Constrexpr.CCases (_, _, _, _) -> term
  | Constrexpr.CLetTuple (_, _, _, _) -> term
  | Constrexpr.CIf (_, _, _, _) -> term
  | Constrexpr.CHole _ -> term
  | Constrexpr.CGenarg _ -> term (* terminal *)
  | Constrexpr.CGenargGlob _ -> term
  | Constrexpr.CPatVar _ -> term
  | Constrexpr.CEvar (existential_name, named_exprs) -> term
  | Constrexpr.CSort _ -> term
  | Constrexpr.CCast (from, cast_kind, to_) -> term
  | Constrexpr.CNotation
      (opt_scope, (notation_entry, notation_key), substitution) ->
      let expr_l1, expr_ll, kinded_cases_pattern_expr_l, local_binders_ll =
        substitution
      in
      let mapped_expr_l = List.map (replace_func new_func_name) expr_l1 in
      let new_subst =
        (mapped_expr_l, expr_ll, kinded_cases_pattern_expr_l, local_binders_ll)
      in
      print_endline notation_key;
      CAst.make
        (Constrexpr.CNotation
           (opt_scope, (notation_entry, notation_key), new_subst))
  | Constrexpr.CGeneralization (bindind_kind, expr) -> term
  | Constrexpr.CPrim _ -> term
  | Constrexpr.CDelimiters (depth, identifier, expr) -> term
  | Constrexpr.CArray (_, _, _, _) -> term

(* this should be a theorem syntax node  *)
let replace_func_f_by_f_long (x : proof) : transformation_step =
  let x_start = x.proposition.range.start in
  let components = Option.get (Proof.get_theorem_components x) in
  let expr = components.expr in
  let qualid = Libnames.qualid_of_string "g_long" in
  let g_long_func = CAst.make (Constrexpr.CRef (qualid, None)) in
  let new_expr = replace_func g_long_func expr in
  let new_components = { components with expr = new_expr } in
  let new_node =
    Proof.syntax_node_from_theorem_components new_components x_start
  in
  print_endline new_node.repr;
  Replace (x.proposition.id, new_node)

let experiment_tactic ~io ~token:_ ~(doc : Doc.t) =
  let parsed_document = Coq_document.parse_document doc in
  let proofs = Result.get_ok (Coq_document.get_proofs parsed_document) in

  let first_proof = List.hd proofs in
  let first_proof_tactics =
    List.filter Syntax_node.is_syntax_node_ast_tactic first_proof.proof_steps
  in
  let first_tactic = List.hd first_proof_tactics in
  let tactic_args =
    Option.get (Syntax_node.get_tactic_raw_generic_arguments first_tactic)
  in

  let exist_query =
    Q_anywhere
      (Q_list_prefix
         [
           Q_atom "CNotation";
           Q_empty;
           Q_list_prefix [ Q_atom "InConstrEntry"; Q_atom "exists _ .. _ , _" ];
         ])
  in

  List.iter
    (fun tac ->
      let args =
        Option.get (Syntax_node.get_tactic_raw_generic_arguments tac)
      in
      let elems =
        Option.get (Raw_gen_args_converter.raw_arguments_to_ltac_elements args)
      in
      if is_raw_assert elems.raw_tactic_expr then (
        let expr = Option.get (get_assert_constr_expr elems.raw_tactic_expr) in

        let sexp_expr = Serlib.Ser_constrexpr.sexp_of_constr_expr expr in

        print_endline (tac.repr ^ " is an assert ");
        if Theorem_query.matches exist_query sexp_expr then
          print_endline "there is an exist inside the assert"))
    first_proof_tactics;

  let elems =
    Option.get
      (Raw_gen_args_converter.raw_arguments_to_ltac_elements tactic_args)
  in

  ()

let experiment_theorem ~io ~token:_ ~(doc : Doc.t) =
  let uri = doc.uri in
  let uri_str = Lang.LUri.File.to_string_uri uri in

  let parsed_document = Coq_document.parse_document doc in
  let proofs = Result.get_ok (Coq_document.get_proofs parsed_document) in

  let first_proof = List.hd proofs in
  Proof.print_proof first_proof;

  let constr_expr = Option.get (Proof.get_constr_expr first_proof) in
  print_info_constr_expr constr_expr;
  let _ = replace_func_f_by_f_long first_proof in

  (* let steps = Transformations.admit_proof parsed_document first_proof in *)

  (* let new_doc_res = *)
  (*   match steps with *)
  (*   | Ok steps -> *)
  (*       List.fold_left *)
  (*         (fun doc_acc_err step -> *)
  (*           match doc_acc_err with *)
  (*           | Ok doc -> Coq_document.apply_transformation_step step doc *)
  (*           | Error err -> Error err) *)
  (*         (Ok parsed_document) steps *)
  (*   | Error err -> Error err *)
  (* in *)

  (* let new_doc = Result.get_ok new_doc_res in *)

  (* List.iter *)
  (*   (fun node -> *)
  (*     print_endline (node.repr ^ " " ^ Lang.Range.to_string node.range)) *)
  (*   new_doc.elements; *)

  (* let filename = Filename.remove_extension uri_str ^ "_bis.v" in *)
  (* print_endline ("All transformations applied, writing to file" ^ filename); *)

  (* let out = open_out filename in *)
  (* output_string out (Coq_document.dump_to_string new_doc); *)
  let first_proof_prop =
    Option.get (Theorem_query.get_proof_proposition_sexp first_proof)
  in

  let theorem_query = Q_list_prefix [ Q_atom "CProdN" ] in

  (* Sexplib.Sexp.pp_hum Format.std_formatter (remove_loc first_proof_prop); *)
  print_newline ();

  print_endline "------------------------";

  let theorem =
    List.hd
      (Theorem_query.collect_matches theorem_query
         (remove_loc first_proof_prop))
  in
  (* Sexplib.Sexp.pp_hum Format.std_formatter theorem; *)
  let last_query = Q_last Q_anything in
  let theorem_end =
    List.hd (Theorem_query.collect_matches last_query theorem)
  in
  Sexplib.Sexp.pp_hum_indent 0 Format.std_formatter theorem_end;
  print_newline ();
  flush_all ();
  ()

let dump_ast ~io ~token:_ ~(doc : Doc.t) =
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
      if List.length errors > 0 then
        let first_errors = List.filteri (fun i _ -> i < 3) errors in
        print_diagnostics first_errors
      else
        let transformations_help =
          [
            ( MakeIntrosExplicit,
              "Transform intros. into intros X_1 ... X_n where X are the \
               variables introduced by intros." );
            ( TurnIntoOneliner,
              "Remove all commands from the proof and turn all steps into a \
               single tactic call using the ';' and '[]' tacticals." );
            ( ReplaceAutoWithSteps,
              "Replace all calls to the 'auto' tactic with the steps \
               effectively used by auto using 'info_auto' trace." );
            ( CompressIntro,
              "Replace consecutive calls to the 'intro' tactic with one call \
               to 'intros'." );
            (IdTransformation, "Keep the file the same.");
          ]
        in

        match Sys.getenv_opt "DITTO_TRANSFORMATION" with
        | Some args ->
            let args = String.split_on_char ',' args in
            let transformations_steps =
              List.filter_map
                (fun x -> Result.to_option (arg_to_transformation_kind x))
                args
            in
            if List.mem Help transformations_steps then
              print_help transformations_help
            else
              let parsed_document = Coq_document.parse_document doc in
              let transformations =
                List.map
                  (transformation_kind_to_function parsed_document)
                  transformations_steps
              in

              let res =
                List.fold_left
                  (fun (doc_acc : Coq_document.t) transformation ->
                    let doc_res =
                      Transformations.apply_proof_transformation transformation
                        doc_acc
                    in
                    match doc_res with
                    | Ok new_doc -> new_doc
                    | Error err -> doc_acc)
                  parsed_document transformations
              in

              let filename = Filename.remove_extension uri_str ^ "_bis.v" in
              print_endline
                ("All transformations applied, writing to file" ^ filename);

              let out = open_out filename in
              output_string out (Coq_document.dump_to_string res);
              ()
        | None ->
            prerr_endline
              "Please specify the wanted transformation using the environment \
               variable: DITTO_TRANSFORMATION";
            prerr_endline
              "If you want help about the different transformation, specify \
               DITTO_TRANSFORMATION=HELP";
            exit 1)

let main () = Theory.Register.Completed.add experiment_theorem
let () = main ()
