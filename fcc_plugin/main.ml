open Fleche
open Ditto
open Ditto.Proof_tree
open Ditto.Proof
open Ditto.Syntax_node
open Vernacexpr

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

let rec print_info_constr_expr_r (x : Constrexpr.constr_expr_r) =
  match x with
  | Constrexpr.CRef (qualid, instance_expr) -> print_qualid qualid
  | Constrexpr.CFix (_, _) -> print_endline "not handled"
  | Constrexpr.CCoFix (_, _) -> print_endline "not handled"
  | Constrexpr.CProdN (binders, expr) ->
      List.iter print_binder_type binders;
      print_info_constr_expr_r expr.v
  | Constrexpr.CLambdaN (_, _) -> print_endline "not handled"
  | Constrexpr.CLetIn (_, _, _, _) -> print_endline "not handled"
  | Constrexpr.CAppExpl (_, _) -> print_endline "not handled"
  | Constrexpr.CApp (_, _) -> print_endline "not handled"
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
        (fun (x : Constrexpr.constr_expr) -> print_info_constr_expr_r x.v)
        expr_l1
  | Constrexpr.CGeneralization (_, _) -> print_endline "not handled"
  | Constrexpr.CPrim prim_token -> print_prim_token prim_token
  | Constrexpr.CDelimiters (_, _, _) -> print_endline "not handled"
  | Constrexpr.CArray (_, _, _, _) -> print_endline "not handled"

type transformation_kind =
  | Help
  | MakeIntrosExplicit
  | TurnIntoOneliner
  | ReplaceAutoWithSteps
  | CompressIntro

let transformation_kind_to_arg (kind : transformation_kind) : string =
  match kind with
  | Help -> "HELP"
  | MakeIntrosExplicit -> "MAKE_INTROS_EXPLICIT"
  | TurnIntoOneliner -> "TURN_INTO_ONELINER"
  | ReplaceAutoWithSteps -> "REPLACE_AUTO_WITH_STEPS"
  | CompressIntro -> "COMPRESS_INTROS"

let arg_to_transformation_kind (arg : string) :
    (transformation_kind, string) result =
  let normalized = String.lowercase_ascii arg in
  if normalized = "help" then Ok Help
  else if normalized = "make_intros_explicit" then Ok MakeIntrosExplicit
  else if normalized = "turn_into_one_liner" then Ok TurnIntoOneliner
  else if normalized = "replace_auto_with_steps" then Ok ReplaceAutoWithSteps
  else if normalized = "compress_intro" then Ok CompressIntro
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

let print_help (transformation_help : (transformation_kind * string) list) :
    unit =
  List.iter
    (fun (kind, help) ->
      print_endline (transformation_kind_to_arg kind ^ ": " ^ help);
      print_newline ())
    transformation_help

let range_to_diag_repr (r : Lang.Range.t) : string =
  "line: " ^ string_of_int r.start.line ^ " char: " ^ string_of_int r.end_.line

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
        ^ range_to_diag_repr diag.range
        ^ " "
        ^ diagnostic_kind_to_str diag.severity
        ^ ": "
        ^ Pp.string_of_ppcmds diag.message))
    errors

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

let main () = Theory.Register.Completed.add dump_ast
let () = main ()
