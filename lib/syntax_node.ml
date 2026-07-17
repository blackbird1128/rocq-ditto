open Fleche
open Vernacexpr

[%%import "rocq_version_optcomp.mlh"]
[%%if rocq_major_version < 9]

module Procq = Pcoq

[%%endif]

type t = {
  ast : Doc.Node.Ast.t option;
  range : Code_range.t;
  repr : string Lazy.t;
  id : Uuidm.t;
  diagnostics : Lang.Diagnostic.t list;
}

let repr (x : t) : string = Lazy.force x.repr

let generate_ast (code : string) :
    (Vernacexpr.vernac_control list, Error.t) result =
  let mode = Ltac_plugin.G_ltac.classic_proof_mode in
  let entry = Pvernac.main_entry (Some mode) in
  let code_stream = Gramlib.Stream.of_string code in
  let init_parser = Procq.Parsable.make code_stream in
  let parse_one () =
    try Ok (Procq.Entry.parse entry init_parser)
    with Gramlib.Grammar.Error exn -> Error (Error.of_string exn)
  in
  let rec parse_all acc =
    match parse_one () with
    | Ok None -> Ok (List.rev acc)
    | Ok (Some ast) -> (parse_all [@tailcall]) (ast :: acc)
    | Error err -> Error err
  in
  parse_all []

let mk_vernac_control ?(loc : Loc.t option)
    (ve : synterp_vernac_expr vernac_expr_gen) : vernac_control =
  let control = [] in
  let attrs = [] in
  let payload = { control; attrs; expr = ve } in
  CAst.make ?loc payload

let inherit_metadata ~(from : t) (node : t) : t =
  { node with id = from.id; diagnostics = from.diagnostics }

let char_span_on_line (r : Code_range.t) (line : int) : int * int =
  (* half-open char span [start_char, end_char) of r on a particular line that r touches *)
  let start_char = if r.start.line < line then 0 else r.start.character in
  let _, end_line_excl = Code_range.line_span r in
  let end_char =
    if end_line_excl > line + 1 then max_int else r.end_.character
  in
  (start_char, end_char)

let are_colliding (a : t) (b : t) : bool =
  let a_ls, a_le = Code_range.line_span a.range in
  let b_ls, b_le = Code_range.line_span b.range in
  (* common line span [cs, ce) *)
  let cs = max a_ls b_ls in
  let ce = min a_le b_le in
  if ce <= cs then false
  else if ce - cs >= 2 then true
  else
    let line = cs in
    let a_cs = char_span_on_line a.range line in
    let b_cs = char_span_on_line b.range line in
    Code_range.are_flat_ranges_colliding a_cs b_cs

let colliding_nodes (target : t) (nodes_list : t list) : t list =
  List.filter (are_colliding target) nodes_list

let compare (a : t) (b : t) : int =
  let c = Code_point.compare a.range.start b.range.start in
  if c <> 0 then c else Code_point.compare a.range.end_ b.range.end_

let count_newlines_and_last_line_len (s : string) : int * int =
  (* returns (number_of_newlines, length_of_last_line_after_last_newline) *)
  let n = String.length s in
  let rec loop (i : int) (newlines : int) (last_len : int) =
    if i >= n then (newlines, last_len)
    else
      match s.[i] with
      | '\n' -> loop (i + 1) (newlines + 1) 0
      | _ -> loop (i + 1) newlines (last_len + 1)
  in
  loop 0 0 0

let validate (x : t) : (t, Error.t) result =
  let r = x.range in
  if r.end_.line < r.start.line then
    Error.string_to_or_error
      "Incorrect range: range end line is smaller than start line"
  else if r.end_.line = r.start.line && r.end_.character < r.start.character
  then
    Error.string_to_or_error
      "Incorrect range: same line but end character < start character"
  else
    let s = repr x in
    let nl, last_len = count_newlines_and_last_line_len s in
    let expected_end_line = r.start.line + nl in
    if r.end_.line <> expected_end_line then
      Error.format_to_or_error
        "Incorrect range: repr has %d newlines, expected end_.line = %d but \
         got %d"
        nl expected_end_line r.end_.line
    else if nl = 0 then
      let expected_end_char = r.start.character + String.length s in
      if r.end_.character <> expected_end_char then
        Error.format_to_or_error
          "Incorrect range: single-line repr length: %d; expect \
           end_.character=%d but got %d"
          (String.length s) expected_end_char r.end_.character
      else Ok x
    else if r.end_.character <> last_len then (* multi line repr *)
      Error.format_to_or_error
        "Incorrect range: multi-line repr last-line length=%d, expected \
         end_.character=%d but got %d"
        last_len last_len r.end_.character
    else Ok x

(* TODO, is this even necessary ? *)
let comment_of_string (content : string) (start_point : Code_point.t) :
    (t, Error.t) result =
  let range =
    Code_range.range_from_starting_point_and_repr start_point content
  in

  if not (String.starts_with ~prefix:"(*" content) then
    Error.format_to_or_error "Content \"%s\" should start with (*" content
  else if not (String.ends_with ~suffix:"*)" content) then
    Error.format_to_or_error "Content \"%s\" should end with *)" content
  else
    Ok
      {
        ast = None;
        repr = lazy content;
        range;
        id = Unique_id.uuid ();
        diagnostics = [];
      }

let syntax_node_of_string (code : string) (start_point : Code_point.t) :
    (t, Error.t) result =
  let range = Code_range.range_from_starting_point_and_repr start_point code in
  (*offset doesn't count the newline in*)

  match generate_ast code with
  | Ok [] -> Error (Error.of_string ("no node found in string " ^ code))
  | Ok [ x ] ->
      let node_ast : Doc.Node.Ast.t =
        { v = Coq.Ast.of_coq x; ast_info = None }
      in

      Ok
        {
          ast = Some node_ast;
          range;
          id = Unique_id.uuid ();
          (*id is set during insertion in a document*)
          repr = lazy code;
          diagnostics = [];
        }
  | Ok (_ :: _ :: _) ->
      Error (Error.of_string ("more than one node found in string " ^ code))
  | Error err -> Error err

let remove_outer_parentheses s =
  let len = String.length s in
  if len >= 2 && s.[0] = '(' && s.[len - 2] = ')' && s.[len - 1] = '.' then
    String.sub s 1 (len - 3) ^ "."
  else s

let node_representation (node : Doc.Node.t) (document : string) : string =
  String.sub document node.range.start.offset
    (node.range.end_.offset - node.range.start.offset)

let of_doc_node (source : string) (node : Doc.Node.t) : t =
  {
    ast = node.ast;
    range = Code_range.code_range_from_lang_range node.range;
    repr = lazy (node_representation node source);
    id = Unique_id.uuid ();
    diagnostics = node.diags;
  }

let of_coq_ast (ast : Coq.Ast.t) (start_point : Code_point.t) : t =
  let coq_ast = Coq.Ast.to_coq ast in

  let repr =
    Ppvernac.pr_vernac coq_ast |> Pp.string_of_ppcmds
    |> remove_outer_parentheses
  in
  let range = Code_range.range_from_starting_point_and_repr start_point repr in
  let node_ast : Doc.Node.Ast.t = { v = ast; ast_info = None } in
  {
    ast = Some node_ast;
    range;
    id = Unique_id.uuid ();
    (* id is set during document insertion *)
    repr = lazy repr;
    diagnostics = [];
  }

let of_coq_ast_in_state ~(token : Coq.Limits.Token.t) ~(st : Coq.State.t)
    (ast : Coq.Ast.t) (start_point : Code_point.t) : (t, Error.t) result =
  let ( let* ) = Result.bind in
  let coq_ast = Coq.Ast.to_coq ast in

  let* repr =
    Coq.State.in_state ~token ~st
      ~f:(fun coq_ast ->
        Ppvernac.pr_vernac coq_ast |> Pp.string_of_ppcmds
        |> remove_outer_parentheses)
      coq_ast
    |> Error.protect_to_result
  in
  let range = Code_range.range_from_starting_point_and_repr start_point repr in
  let node_ast : Doc.Node.Ast.t = { v = ast; ast_info = None } in
  Ok
    {
      ast = Some node_ast;
      range;
      id = Unique_id.uuid ();
      (* id is set during document insertion *)
      repr = lazy repr;
      diagnostics = [];
    }

let of_vernacexpr (expr : Vernacexpr.vernac_expr) (start_point : Code_point.t) :
    t =
  let vernac_control = mk_vernac_control expr in
  let ast = Coq.Ast.of_coq vernac_control in
  of_coq_ast ast start_point

let of_vernacexpr_in_state ~(token : Coq.Limits.Token.t) ~(st : Coq.State.t)
    (expr : Vernacexpr.vernac_expr) (start_point : Code_point.t) :
    (t, Error.t) result =
  let vernac_control = mk_vernac_control expr in
  let ast = Coq.Ast.of_coq vernac_control in
  of_coq_ast_in_state ~token ~st ast start_point

let reformat_node (x : t) : (t, Error.t) result =
  match x.ast with
  | Some ast ->
      let start_point = x.range.start in
      let ast_node = of_coq_ast ast.v start_point in
      Ok (inherit_metadata ~from:x ast_node)
      (* we return the same id, doesn't matter in the order of operation we do *)
  | None ->
      Error.string_to_or_error "The node need to have an AST to be reformatted"

let shift_node (n_line : int) (n_char : int) (x : t) : t =
  { x with range = Code_range.shift n_line n_char x.range }

let vernac_expr (x : t) =
  Option.map (fun (ast : Doc.Node.Ast.t) -> (Coq.Ast.to_coq ast.v).v.expr) x.ast

let synpure_expr (x : t) =
  match vernac_expr x with
  | Some (VernacSynPure expr) -> Some expr
  | Some (VernacSynterp _) | None -> None

let synterp_expr (x : t) =
  match vernac_expr x with
  | Some (VernacSynterp expr) -> Some expr
  | Some (VernacSynPure _) | None -> None

let is_command_allowed_in_proof (x : t) : bool =
  match synpure_expr x with
  (* Proof structuring *)
  | Some
      ( VernacProof _ | VernacEndProof _ | VernacAbort | VernacAbortAll
      | VernacRestart | VernacUndo _ | VernacUndoTo _ | VernacBack _
      | VernacFocus _ | VernacUnfocus | VernacUnfocused | VernacBullet _
      | VernacSubproof _ | VernacEndSubproof
      (* Queries / utilities *)
      | VernacShow _ | VernacCheckMayEval _ | VernacGlobalCheck _
      | VernacPrint _ | VernacSearch _ | VernacLocate _
      (* internal or rare ? *)
      | VernacExactProof _ | VernacValidateProof | VernacCheckGuard ) ->
      true
  | Some _ | None -> false

let is_ltac (x : t) : bool =
  match synterp_expr x with
  | Some (VernacExtend (ext, _)) ->
      ext.ext_plugin = Rocq_version.ltac_ext_plugin_name
  | Some _ | None -> false

let is_proof_command (x : t) : bool =
  match synpure_expr x with Some (VernacProof _) -> true | _ -> false

let is_proof_with (x : t) : bool =
  match synpure_expr x with
  | Some (VernacProof (Some _, _)) -> true
  | _ -> false

[%%if rocq_version <= (9, 0, 1)]

let get_proof_with_tactic (x : t) : string option =
  match synpure_expr x with
  | Some (VernacProof (Some raw_arg, _)) ->
      let empty_env = Environ.empty_env in
      let empty_evd = Evd.empty in
      Some
        (Pp.string_of_ppcmds
           (Pputils.pr_raw_generic empty_env empty_evd raw_arg))
  | _ -> None

[%%else]

let get_proof_with_tactic (x : t) : string option =
  match synpure_expr x with
  | Some (VernacProof (Some raw_arg, _)) ->
      let empty_env = Environ.empty_env in
      let empty_evd = Evd.empty in
      Some
        (Pp.string_of_ppcmds
           (Pputils.pr_raw_generic empty_env empty_evd
              (Gentactic.to_raw_genarg raw_arg)))
  | _ -> None

[%%endif]

let is_ending_with_ellipsis (x : t) : bool =
  String.ends_with ~suffix:"..." (repr x)

let is_context (x : t) : bool =
  match synpure_expr x with Some (VernacContext _) -> true | _ -> false

let is_require (x : t) : bool =
  match synterp_expr x with Some (VernacRequire _) -> true | _ -> false

let is_function_start (x : t) : bool =
  match synterp_expr x with
  | Some (VernacExtend (ext, _)) ->
      ext.ext_plugin = Rocq_version.ltac_funid_plugin_name
      && ext.ext_entry = "Function"
  | _ -> false

let is_instance_start (x : t) : bool =
  match synpure_expr x with Some (VernacInstance _) -> true | _ -> false

let is_program_instance_start (x : t) : bool =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).v.expr with
      | VernacSynterp _ -> false
      | VernacSynPure expr -> (
          match expr with
          | Vernacexpr.VernacInstance _ ->
              let flags = (Coq.Ast.to_coq ast.v).v.attrs in
              List.exists
                (fun (flag : Attributes.vernac_flag) ->
                  let str, _ = flag.v in
                  String.equal str "program")
                flags
          | _ -> false))
  | None -> false

let is_definition (x : t) : bool =
  match synpure_expr x with Some (VernacDefinition _) -> true | _ -> false

let is_goal (x : t) : bool =
  match synpure_expr x with
  | Some
      (VernacDefinition
         ((NoDischarge, Decls.Definition), (lname, _), definition_expr)) -> (
      lname.v = Names.Anonymous
      && match definition_expr with ProveBody _ -> true | _ -> false)
  | _ -> false

let is_definition_with_proof (x : t) : bool =
  (* TODO: check if this include anonymous goals *)
  match synpure_expr x with
  | Some (VernacDefinition ((_, _), _, ProveBody _)) -> true
  | _ -> false

let get_definition_name (x : t) : string option =
  match synpure_expr x with
  | Some (VernacDefinition (_, (name, _), _)) ->
      Some (Pp.string_of_ppcmds (Names.Name.print name.v))
  | _ -> None

let get_definition_constrexpr (x : t) : Constrexpr.constr_expr option =
  match synpure_expr x with
  | Some (VernacDefinition (_, _, DefineBody (_, _, expr, _))) -> Some expr
  | _ -> None

let is_bullet (x : t) : bool =
  match synpure_expr x with Some (VernacBullet _) -> true | _ -> false

let is_opening_bracket (x : t) : bool =
  match synpure_expr x with Some (VernacSubproof _) -> true | _ -> false

let is_closing_bracket (x : t) : bool =
  match synpure_expr x with Some VernacEndSubproof -> true | _ -> false

let is_focus_command (x : t) : bool =
  match synpure_expr x with Some (VernacFocus _) -> true | _ -> false

let is_focusing_goal (x : t) : bool =
  is_bullet x || is_focus_command x || is_opening_bracket x

let is_proof_start (x : t) : bool =
  match synpure_expr x with
  | Some (VernacStartTheoremProof _) -> true
  | _ -> false

let is_proof_end (x : t) : bool =
  match synpure_expr x with Some (VernacEndProof _) -> true | _ -> false

let is_proof_abort (x : t) : bool =
  match synpure_expr x with
  | Some (VernacAbort | VernacAbortAll) -> true
  | _ -> false

let get_extend_name (x : t) : extend_name option =
  match synterp_expr x with
  | Some (VernacExtend (ext, _)) -> Some ext
  | _ -> None

let get_tactic_raw_generic_arguments (x : t) :
    Genarg.raw_generic_argument list option =
  match synterp_expr x with
  | Some (VernacExtend (ext, args))
    when ext.ext_plugin = Rocq_version.ltac_ext_plugin_name ->
      Some args
  | _ -> None

open Raw_gen_args_converter

let get_ltac_elements (x : t) : ltac_elements option =
  get_tactic_raw_generic_arguments x
  |> Option.map raw_arguments_to_ltac_elements
  |> Option.flatten

let get_goal_selector_opt (x : t) : Goal_select_view.t option =
  get_tactic_raw_generic_arguments x
  |> Option.map raw_arguments_to_goal_selector
  |> Option.flatten

let get_raw_tactic_expr (x : t) : Ltac_plugin.Tacexpr.raw_tactic_expr option =
  get_tactic_raw_generic_arguments x
  |> Option.map raw_arguments_to_raw_tactic_expr
  |> Option.flatten

let get_raw_tactic_expr_view (x : t) :
    Ltac_plugin.Tacexpr.r_dispatch Ltac_plugin.Tacexpr.gen_tactic_expr_r option
    =
  get_raw_tactic_expr x
  |> Option.map (fun (expr : Ltac_plugin.Tacexpr.raw_tactic_expr) -> expr.v)

let get_tacdef_bodies (x : t) : Ltac_plugin.Tacexpr.tacdef_body list option =
  get_tactic_raw_generic_arguments x
  |> Option.map raw_arguments_to_tacdef_bodies
  |> Option.flatten

let string_to_raw_tactic_expr (str : string) :
    (Ltac_plugin.Tacexpr.raw_tactic_expr, Error.t) result =
  let ( let* ) = Result.bind in
  let* node = syntax_node_of_string str Code_point.dummy in
  match get_raw_tactic_expr node with
  | Some e -> Ok e
  | None ->
      Error.format_to_or_error
        "%s isn't convertible to a raw_tactic_expr (It probably isn't valid \
         Ltac)"
        str

let get_raw_atomic_tactic_expr (x : t) :
    Ltac_plugin.Tacexpr.raw_atomic_tactic_expr option =
  let raw_expr = get_raw_tactic_expr x in
  Option.map Ltac.get_raw_atomic_tactic_expr raw_expr |> Option.flatten

let tactic_raw_generic_arguments_to_syntax_node (ext : extend_name)
    (args : Genarg.raw_generic_argument list) (starting_point : Code_point.t) :
    t option =
  match args with
  | [ _; _; _; _ ] ->
      let expr_syn = Vernacexpr.VernacExtend (ext, args) in
      let synterp_expr = Vernacexpr.VernacSynterp expr_syn in
      let control = mk_vernac_control synterp_expr in
      let ast_node = Coq.Ast.of_coq control in
      Some (of_coq_ast ast_node starting_point)
  | _ -> None

let tactic_raw_generic_arguments_to_syntax_node_in_state
    ~(token : Coq.Limits.Token.t) ~(st : Coq.State.t) (ext : extend_name)
    (args : Genarg.raw_generic_argument list) (starting_point : Code_point.t) :
    (t option, Error.t) result =
  let ( let* ) = Result.bind in
  match args with
  | [ _; _; _; _ ] ->
      let expr_syn = Vernacexpr.VernacExtend (ext, args) in
      let synterp_expr = Vernacexpr.VernacSynterp expr_syn in
      let control = mk_vernac_control synterp_expr in
      let ast_node = Coq.Ast.of_coq control in
      let* new_node = of_coq_ast_in_state ~token ~st ast_node starting_point in
      Ok (Some new_node)
  | _ -> Ok None

let tacdef_body_raw_generic_argument_to_syntax_node
    (args : Genarg.raw_generic_argument list) (starting_point : Code_point.t) :
    t option =
  match args with
  | [ _ ] ->
      let expr_syn =
        Vernacexpr.VernacExtend (Ltac.ltac_definition_extend_name, args)
      in
      let synterpr_expr = Vernacexpr.VernacSynterp expr_syn in
      let control = mk_vernac_control synterpr_expr in
      let ast_node = Coq.Ast.of_coq control in
      Some (of_coq_ast ast_node starting_point)
  | _ -> None

let tacdef_body_list_to_syntax_node
    (td_list : Ltac_plugin.Tacexpr.tacdef_body list)
    (starting_point : Code_point.t) : (t, Error.t) result =
  let args =
    [ Raw_gen_args_converter.raw_generic_argument_of_tacdef_bodies td_list ]
  in
  match tacdef_body_raw_generic_argument_to_syntax_node args starting_point with
  | Some tac -> Ok tac
  | None ->
      Error.string_to_or_error
        "Error creating a syntax node from the provided tacdef_body list"

let raw_tactic_expr_to_syntax_node
    (raw_expr : Ltac_plugin.Tacexpr.raw_tactic_expr)
    ?(selector : Goal_select_view.t option) ?(use_default = false)
    (starting_point : Code_point.t) : (t, Error.t) result =
  let args =
    [
      Raw_gen_args_converter.raw_generic_argument_of_ltac_selector selector;
      Raw_gen_args_converter.raw_generic_argument_of_empty_ltac_info ();
      Raw_gen_args_converter.raw_generic_argument_of_raw_tactic_expr raw_expr;
      Raw_gen_args_converter.raw_generic_argument_of_ltac_use_default
        use_default;
    ]
  in

  match
    tactic_raw_generic_arguments_to_syntax_node Ltac.ltac_tactic_extend_name
      args starting_point
  with
  | Some tac -> Ok tac
  | None ->
      let env = Global.env () in
      let evd = Evd.from_env env in

      let pp_str =
        Ltac_plugin.Pptactic.pr_raw_tactic env evd raw_expr
        |> Pp.string_of_ppcmds
      in
      Error.format_to_or_error "Error creating a syntax node from %s" pp_str

let raw_tactic_expr_to_syntax_node_in_state ~(token : Coq.Limits.Token.t)
    ~(st : Coq.State.t) (raw_expr : Ltac_plugin.Tacexpr.raw_tactic_expr)
    ?(selector : Goal_select_view.t option) ?(use_default = false)
    (starting_point : Code_point.t) : (t, Error.t) result =
  let ( let* ) = Result.bind in
  let args =
    [
      Raw_gen_args_converter.raw_generic_argument_of_ltac_selector selector;
      Raw_gen_args_converter.raw_generic_argument_of_empty_ltac_info ();
      Raw_gen_args_converter.raw_generic_argument_of_raw_tactic_expr raw_expr;
      Raw_gen_args_converter.raw_generic_argument_of_ltac_use_default
        use_default;
    ]
  in
  match
    tactic_raw_generic_arguments_to_syntax_node_in_state ~token ~st
      Ltac.ltac_tactic_extend_name args starting_point
  with
  | Ok (Some tac) -> Ok tac
  | Ok None ->
      let* repr =
        Coq.State.in_state ~token ~st
          ~f:(fun raw_expr ->
            let env = Global.env () in
            let evd = Evd.from_env env in
            Ltac_plugin.Pptactic.pr_raw_tactic env evd raw_expr
            |> Pp.string_of_ppcmds |> remove_outer_parentheses)
          raw_expr
        |> Error.protect_to_result
      in

      Error.format_to_or_error "Error creating a syntax node from %s" repr
  | Error err -> Error err

let drop_goal_selector (x : t) : t =
  match get_tactic_raw_generic_arguments x with
  | Some [ _sel; a1; a2; a3 ] ->
      let args = raw_generic_argument_of_ltac_selector None :: [ a1; a2; a3 ] in
      let syntax_node_from_raw_gen_args =
        tactic_raw_generic_arguments_to_syntax_node Ltac.ltac_tactic_extend_name
          args x.range.start
        |> Option.map (inherit_metadata ~from:x)
      in
      Option.default x syntax_node_from_raw_gen_args
  | _ -> x

let add_goal_selector (x : t) (selector : Goal_select_view.t) :
    (t, Error.t) result =
  match get_goal_selector_opt x with
  | Some selector ->
      Error.format_to_or_error "%s already contains a goal selector: %s"
        (repr x)
        (Goal_select_view.to_string selector)
  | None -> (
      match get_raw_tactic_expr x with
      | Some expr ->
          raw_tactic_expr_to_syntax_node expr ~selector x.range.start
          |> Result.map (inherit_metadata ~from:x)
      | None ->
          Error.format_to_or_error
            "%s isn't convertible to a raw_tactic_expr (It probably isn't Ltac)"
            (repr x))

let is_assumption (x : t) : bool =
  match get_raw_tactic_expr_view x with
  | Some (Ltac_plugin.Tacexpr.TacArg (TacCall call)) ->
      let qualid, args = call.v in
      args = []
      && Names.Id.equal
           (Libnames.qualid_basename qualid)
           (Names.Id.of_string "assumption")
  | _ -> false

let is_intros (x : t) : bool =
  match get_raw_atomic_tactic_expr x with
  | Some (Ltac_plugin.Tacexpr.TacIntroPattern _) -> true
  | _ -> false

let is_assert (x : t) : bool =
  match get_raw_atomic_tactic_expr x with
  | Some (Ltac_plugin.Tacexpr.TacAssert _) -> true
  | _ -> false

let is_assert_by (x : t) : bool =
  match get_raw_atomic_tactic_expr x with
  | Some (Ltac_plugin.Tacexpr.TacAssert (false, true, Some (Some _), _, _)) ->
      true
  | _ -> false

let get_assert_expr (x : t) : Constrexpr.constr_expr option =
  match get_raw_atomic_tactic_expr x with
  | Some (TacAssert (false, true, _, _, expr)) -> Some expr
  | _ -> None

let get_assert_by_raw_tac_expr (x : t) :
    Ltac_plugin.Tacexpr.raw_tactic_expr option =
  match get_raw_atomic_tactic_expr x with
  | Some (Ltac_plugin.Tacexpr.TacAssert (false, true, Some (Some expr), _, _))
    ->
      Some expr
  | _ -> None

(* single-pass validation + conversion *)
let l_to_raw_tactics (l : t list) =
  let rec aux (acc : Ltac_plugin.Tacexpr.raw_tactic_expr list) (i : int) =
    function
    | [] -> Ok (List.rev acc)
    | x :: xs -> (
        match get_raw_tactic_expr x with
        | Some raw -> aux (raw :: acc) (i + 1) xs
        | None ->
            Error.format_to_or_error
              "%s at index %d in l isn't convertible to a raw_tactic_expr (It \
               probably isn't Ltac)"
              (repr x) i)
  in
  aux [] 0 l

let apply_tac_thens (a : t) (l : t list)
    ?(start_point : Code_point.t = a.range.start) () : (t, Error.t) result =
  let ( let* ) = Result.bind in
  let* raw_a =
    match get_raw_tactic_expr a with
    | Some r -> Ok r
    | None ->
        Error.format_to_or_error
          "%s isn't convertible to a raw_tactic_expr (It probably isn't Ltac)"
          (repr a)
  in

  let* raw_tactics_l = l_to_raw_tactics l in

  let args = get_tactic_raw_generic_arguments a |> Option.get in
  let extend = Ltac.ltac_tactic_extend_name in

  let a_thens_l : Ltac_plugin.Tacexpr.raw_tactic_expr =
    CAst.make (Ltac_plugin.Tacexpr.TacThens (raw_a, raw_tactics_l))
  in

  let raw_arg =
    Raw_gen_args_converter.raw_generic_argument_of_raw_tactic_expr a_thens_l
  in
  let new_args =
    [ List.nth args 0; List.nth args 1; raw_arg; List.nth args 3 ]
  in

  tactic_raw_generic_arguments_to_syntax_node extend new_args start_point
  |> Option.cata Result.ok
       (Error.format_to_or_error "failed to create a thens between %s and [%s]"
          (repr a)
          (l |> List.map repr |> String.concat "; "))

let apply_tac_then (a : t) (b : t) ?(start_point : Code_point.t = a.range.start)
    () : (t, Error.t) result =
  let ( let* ) = Result.bind in

  let* raw_a =
    match get_raw_tactic_expr a with
    | Some r -> Ok r
    | None ->
        Error.format_to_or_error
          "%s isn't convertible to a raw_tactic_expr (It probably isn't Ltac)"
          (repr a)
  in
  let* raw_b =
    match get_raw_tactic_expr b with
    | Some r -> Ok r
    | None ->
        Error.format_to_or_error
          "%s isn't convertible to a raw_tactic_expr (It probably isn't Ltac)"
          (repr b)
  in

  let args = get_tactic_raw_generic_arguments a |> Option.get in
  let extend = Ltac.ltac_tactic_extend_name in

  let a_then_b = Ltac_plugin.Tacexpr.TacThen (raw_a, raw_b) |> CAst.make in
  let raw_arg =
    Raw_gen_args_converter.raw_generic_argument_of_raw_tactic_expr a_then_b
  in
  let new_args =
    [ List.nth args 0; List.nth args 1; raw_arg; List.nth args 3 ]
  in
  tactic_raw_generic_arguments_to_syntax_node extend new_args start_point
  |> Option.cata Result.ok
       (Error.format_to_or_error "failed to create a then betwen %s and %s"
          (repr a) (repr b))

let can_open_proof (x : t) : bool =
  let res =
    is_proof_start x || is_definition_with_proof x
    || (is_instance_start x && not (is_program_instance_start x))
       (* TODO actually treat Program and Obligation *)
    || is_function_start x
  in
  res

let can_close_proof (x : t) : bool = is_proof_abort x || is_proof_end x

let is_proof_intro_or_end (x : t) : bool =
  is_proof_start x || is_proof_command x || is_proof_end x
