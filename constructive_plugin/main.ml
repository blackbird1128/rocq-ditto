open Fleche
open Ditto
open Ditto.Proof_tree
open Ditto.Proof
open Ditto.Syntax_node
open Ditto.Diagnostic_utils
open Vernacexpr
open Theorem_query

let wrap_to_treeify doc x = Result.get_ok (Runner.treeify_proof doc x)

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

let rec get_basic_tactic_names (tac : Ltac_plugin.Tacexpr.raw_tactic_expr) :
    string list =
  let empty_env = Environ.empty_env in
  let empty_evd = Evd.empty in
  let pp = Ltac_plugin.Pptactic.pr_raw_tactic empty_env empty_evd tac in
  match tac.v with
  | Ltac_plugin.Tacexpr.TacAtom atom -> [ Pp.string_of_ppcmds pp ]
  | Ltac_plugin.Tacexpr.TacThen (tac1, tac2) ->
      (*x ; y can be nested*)
      get_basic_tactic_names tac1 @ get_basic_tactic_names tac2
  | Ltac_plugin.Tacexpr.TacDispatch tactics ->
      List.concat_map get_basic_tactic_names tactics
  (* [|>]*)
  | Ltac_plugin.Tacexpr.TacExtendTac (_, _, _) ->
      prerr_endline "extend tac, not handled yet";
      []
  | Ltac_plugin.Tacexpr.TacThens (tacDistributed, tac_list) ->
      (* x;[a;b;c] *)
      get_basic_tactic_names tacDistributed
      @ List.concat_map get_basic_tactic_names tac_list
  | Ltac_plugin.Tacexpr.TacThens3parts (tac1, tac_array1, tac2, tac_array2) ->
      let tac_array1_names =
        Array.map get_basic_tactic_names tac_array1
        |> Array.map Array.of_list |> Array.to_list |> Array.concat
        |> Array.to_list
      in
      let tac_array2_names =
        Array.map get_basic_tactic_names tac_array2
        |> Array.map Array.of_list |> Array.to_list |> Array.concat
        |> Array.to_list
      in
      print_endline "tacThens3parts not handled yet";
      get_basic_tactic_names tac1
      @ tac_array1_names
      @ get_basic_tactic_names tac2
      @ tac_array2_names
  | Ltac_plugin.Tacexpr.TacFirst tac_list ->
      List.concat_map get_basic_tactic_names tac_list
  | Ltac_plugin.Tacexpr.TacSolve tac_to_tries ->
      List.concat_map get_basic_tactic_names tac_to_tries
  | Ltac_plugin.Tacexpr.TacTry expr -> get_basic_tactic_names expr
  | Ltac_plugin.Tacexpr.TacOr (tac1, tac2) ->
      get_basic_tactic_names tac1 @ get_basic_tactic_names tac2
  | Ltac_plugin.Tacexpr.TacOnce tac ->
      get_basic_tactic_names tac (* once tactic*)
  | Ltac_plugin.Tacexpr.TacExactlyOnce tac -> get_basic_tactic_names tac
  | Ltac_plugin.Tacexpr.TacIfThenCatch (_, _, _) ->
      print_endline "tacIfThenCatch not handled yet";
      []
  | Ltac_plugin.Tacexpr.TacOrelse (tac, tac_or_else) ->
      get_basic_tactic_names tac @ get_basic_tactic_names tac_or_else
  | Ltac_plugin.Tacexpr.TacDo (_, tactic_to_do) ->
      get_basic_tactic_names tactic_to_do
  | Ltac_plugin.Tacexpr.TacTimeout (duration, tac) -> get_basic_tactic_names tac
  | Ltac_plugin.Tacexpr.TacTime (_, tacticTimed) ->
      get_basic_tactic_names tacticTimed
  | Ltac_plugin.Tacexpr.TacRepeat tactic_repeated ->
      get_basic_tactic_names tactic_repeated
  | Ltac_plugin.Tacexpr.TacProgress tac -> get_basic_tactic_names tac
  | Ltac_plugin.Tacexpr.TacAbstract (tac, _) -> get_basic_tactic_names tac
  | Ltac_plugin.Tacexpr.TacId msg -> [ "idtac" ]
  | Ltac_plugin.Tacexpr.TacFail (_, _, _) -> [ Pp.string_of_ppcmds pp ]
  | Ltac_plugin.Tacexpr.TacLetIn (_, _, _) ->
      print_endline "tacLetIn not handled yet";
      []
  | Ltac_plugin.Tacexpr.TacMatch (_, _, _) ->
      print_endline "tac match not handled yet";
      []
  | Ltac_plugin.Tacexpr.TacMatchGoal (_, _, _) ->
      print_endline "tac match goal not handled yet";
      []
  | Ltac_plugin.Tacexpr.TacFun l ->
      print_endline "fun call not handled yet";
      []
  | Ltac_plugin.Tacexpr.TacArg arg -> [ Pp.string_of_ppcmds pp ]
  | Ltac_plugin.Tacexpr.TacSelect (goal_select, tac) ->
      get_basic_tactic_names tac
  | Ltac_plugin.Tacexpr.TacML (_, list_tac) ->
      print_endline "what is a tac Ml ? ";
      []
  | Ltac_plugin.Tacexpr.TacAlias (_, tactics) -> [ Pp.string_of_ppcmds pp ]

let rec print_tactic_names (tac : Ltac_plugin.Tacexpr.raw_tactic_expr) : unit =
  let empty_env = Environ.empty_env in
  let empty_evd = Evd.empty in
  let pp = Ltac_plugin.Pptactic.pr_raw_tactic empty_env empty_evd tac in
  print_endline (Pp.string_of_ppcmds pp);
  match tac.v with
  | Ltac_plugin.Tacexpr.TacAtom atom -> print_endline "atom"
  | Ltac_plugin.Tacexpr.TacThen (tac1, tac2) ->
      (*x ; y can be nested*)
      print_endline "tacThen";
      print_tactic_names tac1;
      print_tactic_names tac2
  | Ltac_plugin.Tacexpr.TacDispatch tactics ->
      print_endline "tacDispatch";
      List.iter print_tactic_names tactics
  (* [|>]*)
  | Ltac_plugin.Tacexpr.TacExtendTac (_, _, _) -> print_endline "tacExtendTac"
  | Ltac_plugin.Tacexpr.TacThens (tacDistributed, tac_list) ->
      print_endline "tacThens" (* x;[a;b;c] *)
  | Ltac_plugin.Tacexpr.TacThens3parts (_, _, _, _) ->
      print_endline "tacThens3parts"
  | Ltac_plugin.Tacexpr.TacFirst tac_list ->
      print_endline "first";
      List.iter print_tactic_names tac_list
  | Ltac_plugin.Tacexpr.TacSolve tac_to_tries -> print_endline "tacSolve"
  | Ltac_plugin.Tacexpr.TacTry expr ->
      print_endline "try this tactic: ";
      print_tactic_names expr
  | Ltac_plugin.Tacexpr.TacOr (tac1, tac2) ->
      print_tactic_names tac1;
      print_tactic_names tac2 (* OR tactic || *)
  | Ltac_plugin.Tacexpr.TacOnce tac -> print_endline "tacOnce" (* once tactic*)
  | Ltac_plugin.Tacexpr.TacExactlyOnce tac ->
      print_endline "tacExactlyOnce" (* exactly once tactic *)
  | Ltac_plugin.Tacexpr.TacIfThenCatch (_, _, _) ->
      print_endline "tacIfThenCatch"
  | Ltac_plugin.Tacexpr.TacOrelse (_, _) -> print_endline "tacOrelse"
  | Ltac_plugin.Tacexpr.TacDo (_, tactic_to_do) ->
      print_endline "the doc tactic"
  | Ltac_plugin.Tacexpr.TacTimeout (duration, tac) -> print_endline "tacTimeout"
  | Ltac_plugin.Tacexpr.TacTime (_, tacticTimed) ->
      print_endline "tacTime";
      print_tactic_names tacticTimed
  | Ltac_plugin.Tacexpr.TacRepeat tactic_repeated ->
      print_endline "repeat tactic";
      print_tactic_names tactic_repeated
  | Ltac_plugin.Tacexpr.TacProgress tac ->
      print_endline "tac progress: try a tac and fail if no progress";
      print_tactic_names tac
  | Ltac_plugin.Tacexpr.TacAbstract (tac, _) ->
      print_endline "the abtract tactic"
  | Ltac_plugin.Tacexpr.TacId msg -> print_endline "idtac"
  | Ltac_plugin.Tacexpr.TacFail (_, _, _) -> print_endline "the fail tactic"
  | Ltac_plugin.Tacexpr.TacLetIn (_, _, _) -> print_endline "tacLetIn"
  | Ltac_plugin.Tacexpr.TacMatch (_, _, _) ->
      print_endline "there is a match tactic apparently"
  | Ltac_plugin.Tacexpr.TacMatchGoal (_, _, _) ->
      print_endline "there is also a match goal tactic"
  | Ltac_plugin.Tacexpr.TacFun l -> print_endline "a fun call"
  | Ltac_plugin.Tacexpr.TacArg arg -> print_endline "tacArg"
  | Ltac_plugin.Tacexpr.TacSelect (goal_select, tac) ->
      print_endline "tacSelect"
  | Ltac_plugin.Tacexpr.TacML (_, list_tac) -> print_endline "what is a tac Ml"
  | Ltac_plugin.Tacexpr.TacAlias (_, tactics) ->
      print_endline "a tactic alias to call one or more tactic ?"

(* let get_tactc_names (tac : Ltac_plugin.Tacexpr.raw_tactic_expr) : string list = *)
(*   match tac.v with *)
(*   | Ltac_plugin.Tacexpr.TacAtom atom -> print_endline "atom" *)
(*   | Ltac_plugin.Tacexpr.TacThen (_, _) -> print_endline "tacThen" *)
(*   | Ltac_plugin.Tacexpr.TacDispatch _ -> print_endline "tacDispatch" *)
(*   | Ltac_plugin.Tacexpr.TacExtendTac (_, _, _) -> print_endline "tacExtendTac" *)
(*   | Ltac_plugin.Tacexpr.TacThens (_, _) -> print_endline "tacThens" *)
(*   | Ltac_plugin.Tacexpr.TacThens3parts (_, _, _, _) -> *)
(*       print_endline "tacThens3parts" *)
(*   | Ltac_plugin.Tacexpr.TacFirst _ -> print_endline "tacFirst" *)
(*   | Ltac_plugin.Tacexpr.TacSolve _ -> print_endline "tacSolve" *)
(*   | Ltac_plugin.Tacexpr.TacTry _ -> print_endline "tacTry" *)
(*   | Ltac_plugin.Tacexpr.TacOr (_, _) -> print_endline "tacOr" *)
(*   | Ltac_plugin.Tacexpr.TacOnce _ -> print_endline "tacOnce" *)
(*   | Ltac_plugin.Tacexpr.TacExactlyOnce _ -> print_endline "tacExactlyOnce" *)
(*   | Ltac_plugin.Tacexpr.TacIfThenCatch (_, _, _) -> *)
(*       print_endline "tacIfThenCatch" *)
(*   | Ltac_plugin.Tacexpr.TacOrelse (_, _) -> print_endline "tacOrelse" *)
(*   | Ltac_plugin.Tacexpr.TacDo (_, _) -> print_endline "tacDo" *)
(*   | Ltac_plugin.Tacexpr.TacTimeout (_, _) -> print_endline "tacTimeout" *)
(*   | Ltac_plugin.Tacexpr.TacTime (_, _) -> print_endline "tacTime" *)
(*   | Ltac_plugin.Tacexpr.TacRepeat _ -> print_endline "tacRepeat" *)
(*   | Ltac_plugin.Tacexpr.TacProgress _ -> print_endline "tacProgress" *)
(*   | Ltac_plugin.Tacexpr.TacAbstract (_, _) -> print_endline "tacAbstract" *)
(*   | Ltac_plugin.Tacexpr.TacId _ -> print_endline "tacId" *)
(*   | Ltac_plugin.Tacexpr.TacFail (_, _, _) -> print_endline "tacFail" *)
(*   | Ltac_plugin.Tacexpr.TacLetIn (_, _, _) -> print_endline "tacLetIn" *)
(*   | Ltac_plugin.Tacexpr.TacMatch (_, _, _) -> print_endline "tacMatch" *)
(*   | Ltac_plugin.Tacexpr.TacMatchGoal (_, _, _) -> print_endline "tacMatchGoal" *)
(*   | Ltac_plugin.Tacexpr.TacFun _ -> print_endline "tacFun" *)
(*   | Ltac_plugin.Tacexpr.TacArg arg -> print_endline "tacArg" *)
(*   | Ltac_plugin.Tacexpr.TacSelect (_, _) -> print_endline "tacSelect" *)
(*   | Ltac_plugin.Tacexpr.TacML (_, _) -> print_endline "tacML" *)
(*   | Ltac_plugin.Tacexpr.TacAlias (_, _) -> print_endline "tacAlias" *)

let rec replace_func_map (old_fun_name : string) (new_fun_name : string)
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

let replace_bet_by_betl (x : proof) : transformation_step option =
  let x_start = x.proposition.range.start in
  let components = Option.get (Proof.get_theorem_components x) in
  let expr = components.expr in

  let replace_by_betl_map = replace_func_map "Bet" "BetL" in
  let new_expr, did_replace =
    Expr_substitution.constr_expr_map replace_by_betl_map expr
  in
  if did_replace then
    let new_components = { components with expr = new_expr } in
    let new_node =
      Proof.syntax_node_from_theorem_components new_components x_start
    in

    Some (Replace (x.proposition.id, new_node))
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
      match replace_if_contains previous_tac new_tac node.repr with
      | Some rep ->
          let new_node =
            Result.get_ok
              (Syntax_node.syntax_node_of_string rep node.range.start)
          in
          Some (Replace (node.id, new_node))
      | None -> None)
    x.proof_steps

let print_require (x : syntaxNode) =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).v.expr with
      | VernacSynterp synterp_expr -> (
          match synterp_expr with
          | VernacRequire
              (option_libname, export_with_cats_opt, libnames_import_list) ->
              let _ = Option.map print_qualid option_libname in
              print_endline
                ("libnames len : "
                ^ string_of_int (List.length libnames_import_list));
              List.iter
                (fun (qualid, filter_import) -> print_qualid qualid)
                libnames_import_list;
              ()
          | _ -> ())
      | VernacSynPure _ -> ())
  | None -> ()

let replace_context (x : syntaxNode) : transformation_step option =
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

let replace_require (x : syntaxNode) : transformation_step option =
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
                    let prefix, postfix =
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

let by_load ~(io : Io.CallBack.t) ~token:tok ~(doc : Doc.t) =
  let diags = List.concat_map (fun (x : Doc.Node.t) -> x.diags) doc.nodes in
  let errors = List.filter Lang.Diagnostic.is_error diags in

  let uri = doc.uri in
  let uri_str = Lang.LUri.File.to_string_uri uri in

  match doc.completed with
  | Doc.Completion.Stopped range_stop ->
      prerr_endline ("parsing stopped at " ^ Lang.Range.to_string range_stop);
      print_diagnostics errors
  | Doc.Completion.Failed range_failed ->
      prerr_endline ("parsing failed at " ^ Lang.Range.to_string range_failed);
      print_diagnostics errors
  | Doc.Completion.Yes _ -> (
      let parsed_document = Coq_document.parse_document doc in
      let require_nodes =
        List.filter Syntax_node.is_syntax_node_require parsed_document.elements
      in
      List.iter (fun x -> print_require x) require_nodes;
      let require_transform_steps =
        List.filter_map replace_require parsed_document.elements
      in
      let context_transform_steps =
        List.filter_map replace_context parsed_document.elements
      in
      let new_doc =
        Coq_document.apply_transformations_steps
          (require_transform_steps @ context_transform_steps)
          parsed_document
        |> Result.get_ok
      in

      let other_doc_path = "../dedukti-tarski-dev/coq/ch04_cong_bet.v" in
      let compiler_args =
        Compile.file_and_plugin_args_to_compiler_args other_doc_path io tok doc
        |> Result.get_ok
      in

      let other_doc = Compile.compile_file compiler_args other_doc_path in

      match other_doc with
      | Ok second_doc -> (
          let other_doc_parsed = Coq_document.parse_document second_doc in
          let other_proofs =
            Coq_document.get_proofs other_doc_parsed |> Result.get_ok
          in
          print_endline "there";
          let proof_replacing_steps =
            List.filter_map
              (fun p ->
                let name = Proof.get_proof_name p |> Option.get in
                let reg = Re.compile (Re.str "__") in
                let new_name = Re.replace_string reg ~by:"_" name in
                print_endline p.proposition.repr;
                match Coq_document.proof_with_name_opt new_name new_doc with
                | Some proof ->
                    Coq_document.replace_proof proof.proposition.id p new_doc
                | None -> None)
              other_proofs
            |> List.concat
          in
          let new_doc =
            Coq_document.apply_transformations_steps proof_replacing_steps
              new_doc
          in
          match new_doc with
          | Ok res ->
              let filename =
                "../private-geocoq/theories/Constructive/"
                ^ (Filename.basename uri_str |> Filename.remove_extension)
                ^ "_bis.v"
              in
              print_endline
                ("All transformations applied, writing to file" ^ filename);
              let out = open_out filename in
              output_string out (Coq_document.dump_to_string res)
          | Error err -> print_endline err)
      | Error err -> (
          match err with
          | Compile.IncorrectURI -> print_endline "incorrect URI"
          | Compile.ParsingStopped (stopped_range, errors) ->
              print_diagnostics errors
          | Compile.ParsingFailed (failed_range, errors) ->
              print_diagnostics errors))

let tactic_count ~io ~token:_ ~(doc : Doc.t) =
  let uri = doc.uri in
  let uri_str = Lang.LUri.File.to_string_uri uri in
  prerr_endline ("treating: " ^ uri_str);
  let diags = List.concat_map (fun (x : Doc.Node.t) -> x.diags) doc.nodes in
  let errors = List.filter Lang.Diagnostic.is_error diags in

  match doc.completed with
  | Doc.Completion.Stopped range_stopped ->
      prerr_endline ("parsing stopped at " ^ Lang.Range.to_string range_stopped);
      print_diagnostics errors
  | Doc.Completion.Failed range_failed ->
      prerr_endline ("parsing failed at " ^ Lang.Range.to_string range_failed);
      print_diagnostics errors
  | Doc.Completion.Yes _ ->
      let parsed_document = Coq_document.parse_document doc in

      let proofs = Result.get_ok (Coq_document.get_proofs parsed_document) in

      let proof_steps = List.concat_map (fun x -> x.proof_steps) proofs in
      let proof_tactics =
        List.filter Syntax_node.is_syntax_node_ast_tactic proof_steps
      in

      let basic_tactics =
        List.concat_map
          (fun node ->
            let raw_args =
              Syntax_node.get_tactic_raw_generic_arguments node |> Option.get
            in
            let ltac_elements =
              Raw_gen_args_converter.raw_arguments_to_ltac_elements raw_args
              |> Option.get
            in

            get_basic_tactic_names ltac_elements.raw_tactic_expr)
          proof_tactics
      in
      let first_word_tactics =
        List.map
          (fun tac -> String.split_on_char ' ' tac |> List.hd)
          basic_tactics
      in
      List.iter print_endline first_word_tactics

let experiment_theorem ~io ~token:_ ~(doc : Doc.t) =
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
      let parsed_document = Coq_document.parse_document doc in

      let proofs = Result.get_ok (Coq_document.get_proofs parsed_document) in

      let exists_query =
        Q_anywhere
          (Q_list_prefix
             [
               Q_atom "CNotation";
               Q_empty;
               Q_list_exact
                 [ Q_atom "InConstrEntry"; Q_atom "exists _ .. _ , _" ];
             ])
      in

      let replace_bet_by_betl_steps =
        List.filter_map (fun proof -> replace_bet_by_betl proof) proofs
      in

      let new_doc =
        Result.get_ok
          (Coq_document.apply_transformations_steps replace_bet_by_betl_steps
             parsed_document)
      in

      let proofs = Result.get_ok (Coq_document.get_proofs parsed_document) in

      let replace_or_by_constructive_or_steps =
        List.filter_map
          (fun proof -> replace_or_by_constructive_or proof)
          proofs
      in

      let new_doc =
        Result.get_ok
          (Coq_document.apply_transformations_steps
             replace_or_by_constructive_or_steps new_doc)
      in

      let proofs = Result.get_ok (Coq_document.get_proofs new_doc) in
      (* replacement can be made into any order *)
      let proof_sexps_pairs =
        List.filter_map
          (fun proof ->
            match Theorem_query.get_proof_proposition_sexp proof with
            | Some sexp -> Some (proof, sexp)
            | None -> None)
          proofs
      in

      let new_doc =
        Result.get_ok
          (List.fold_left
             (fun doc_acc (proof, proof_sexps) ->
               match doc_acc with
               | Ok doc_acc ->
                   if Theorem_query.matches exists_query proof_sexps then
                     let steps =
                       Result.get_ok (Transformations.admit_proof doc_acc proof)
                     in
                     Coq_document.apply_transformations_steps steps doc_acc
                   else Ok doc_acc
               | Error err -> Error err)
             (Ok new_doc) proof_sexps_pairs)
      in

      let proofs = Result.get_ok (Coq_document.get_proofs new_doc) in

      let replace_tactics_steps =
        List.concat_map
          (fun proof ->
            List.concat
              [
                replace_tactic_by_other "left" "stab_left" proof;
                replace_tactic_by_other "right" "stab_right" proof;
                replace_tactic_by_other "segment_construction"
                  "apply by segment_construction" proof;
                replace_tactic_by_other "inner_pasch" "apply by_inner_pasch"
                  proof;
              ])
          proofs
      in

      let new_doc =
        Coq_document.apply_transformations_steps replace_tactics_steps new_doc
      in

      match new_doc with
      | Ok res ->
          let filename = Filename.remove_extension uri_str ^ "_bis.v" in
          print_endline
            ("All transformations applied, writing to file" ^ filename);
          let out = open_out filename in
          output_string out (Coq_document.dump_to_string res)
      | Error err ->
          print_endline err;

          ())

let main () = Theory.Register.Completed.add tactic_count
let () = main ()
