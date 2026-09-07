open Fleche
open Vernacexpr

[%%import "rocq_version_optcomp.mlh"]
[%%if rocq_major_version < 9]

module Procq = Pcoq

[%%endif]

type kind = Vernac of Doc.Node.Ast.t | Comment

type t = {
  kind : kind;
  range : Code_range.t;
  repr : string;
  id : Uuidm.t;
  diagnostics : Lang.Diagnostic.t list;
}

let ( let* ) = Result.bind
let equal (a : t) (b : t) = Uuidm.equal a.id b.id
let repr (x : t) : string = x.repr

let make ?(ast = None) ?(diagnostics = []) (start_point : Code_point.t)
    (repr : string) : t =
  let range = Code_range.extent_of_string start_point repr in
  match ast with
  | Some ast ->
      { kind = Vernac ast; range; repr; id = Unique_id.uuid (); diagnostics }
  | None -> { kind = Comment; range; repr; id = Unique_id.uuid (); diagnostics }

let is_vernacular (x : t) : bool =
  match x.kind with Comment -> false | Vernac _ -> true

let is_comment (x : t) : bool =
  match x.kind with Comment -> true | Vernac _ -> false

let expect_vernacular (x : t) : (Doc.Node.Ast.t, Error.t) result =
  match x.kind with
  | Vernac ast -> Ok ast
  | Comment ->
      Error.format_to_or_error
        "Node: %S, expected a vernacular node, got a comment" (repr x)

let generate_ast (code : string) :
    (Vernacexpr.vernac_control list, Error.t) result =
  let mode = Ltac_plugin.G_ltac.classic_proof_mode in
  let entry = Pvernac.main_entry (Some mode) in
  let code_stream = Gramlib.Stream.of_string code in
  let init_parser = Procq.Parsable.make code_stream in
  let parse_one () =
    try Ok (Procq.Entry.parse entry init_parser)
    with Gramlib.Grammar.Error exn -> Error.string_to_or_error exn
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

let are_colliding (a : t) (b : t) : bool =
  Code_range.are_colliding a.range b.range

let colliding_nodes (target : t) (nodes_list : t list) : t list =
  List.filter (are_colliding target) nodes_list

let compare (a : t) (b : t) : int = Code_range.compare a.range b.range

let validate (x : t) : (t, Error.t) result =
  let expected_range = Code_range.extent_of_string x.range.start x.repr in
  if not (Code_range.equal x.range expected_range) then
    Error.format_to_or_error
      "validation error: node(%s) expected range %S got range %S" (repr x)
      (Code_range.to_string expected_range)
      (Code_range.to_string x.range)
  else Ok x

let comment_of_string (content : string) (start_point : Code_point.t) :
    (t, Error.t) result =
  if not (String.starts_with ~prefix:"(*" content) then
    Error.format_to_or_error "Content \"%s\" should start with (*" content
  else if not (String.ends_with ~suffix:"*)" content) then
    Error.format_to_or_error "Content \"%s\" should end with *)" content
  else Ok (make ~ast:None start_point content)

let syntax_node_of_string (code : string) (start_point : Code_point.t) :
    (t, Error.t) result =
  (*offset doesn't count the newline in*)
  match generate_ast code with
  | Ok [] -> Error.format_to_or_error "No node found in string \"%s\"." code
  | Ok [ x ] ->
      let node_ast : Doc.Node.Ast.t =
        { v = Coq.Ast.of_coq x; ast_info = None }
      in
      Ok (make ~ast:(Some node_ast) start_point code)
  | Ok (_ :: _ :: _) ->
      Error.format_to_or_error "More than one node found in string \"%s\"." code
  | Error err -> Error err

let remove_outer_parentheses (s : string) =
  let len = String.length s in
  if len >= 2 && s.[0] = '(' && s.[len - 2] = ')' && s.[len - 1] = '.' then
    String.sub s 1 (len - 3) ^ "."
  else s

let node_representation (node : Doc.Node.t) (document : string) : string =
  String.sub document node.range.start.offset
    (node.range.end_.offset - node.range.start.offset)

let of_doc_node (source : string) (node : Doc.Node.t) : t =
  match node.ast with
  | Some ast ->
      {
        kind = Vernac ast;
        range = Code_range.of_lang_range node.range;
        repr = node_representation node source;
        id = Unique_id.uuid ();
        diagnostics = node.diags;
      }
  | None ->
      {
        kind = Comment;
        range = Code_range.of_lang_range node.range;
        repr = node_representation node source;
        id = Unique_id.uuid ();
        diagnostics = node.diags;
      }

let of_coq_ast (ast : Coq.Ast.t) (start_point : Code_point.t) : t =
  let coq_ast = Coq.Ast.to_coq ast in

  let repr =
    Ppvernac.pr_vernac coq_ast |> Pp.string_of_ppcmds
    |> remove_outer_parentheses
  in

  let node_ast : Doc.Node.Ast.t = { v = ast; ast_info = None } in
  make ~ast:(Some node_ast) start_point repr

let of_coq_ast_in_state ~(token : Coq.Limits.Token.t) ~(st : Coq.State.t)
    (ast : Coq.Ast.t) (start_point : Code_point.t) : (t, Error.t) result =
  let coq_ast = Coq.Ast.to_coq ast in

  let* repr =
    Coq.State.in_state ~token ~st
      ~f:(fun coq_ast ->
        Ppvernac.pr_vernac coq_ast |> Pp.string_of_ppcmds
        |> remove_outer_parentheses)
      coq_ast
    |> Error.protect_to_result
  in

  let node_ast : Doc.Node.Ast.t = { v = ast; ast_info = None } in
  Ok (make ~ast:(Some node_ast) start_point repr)

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

let reformat (x : t) : (t, Error.t) result =
  match x.kind with
  | Vernac ast ->
      let start_point = x.range.start in
      let ast_node = of_coq_ast ast.v start_point in
      Ok (inherit_metadata ~from:x ast_node)
      (* we return the same id, doesn't matter in the order of operation we do *)
  | Comment ->
      Error.string_to_or_error "The node need to have an AST to be reformatted"

let move_to (destination : Code_point.t) (x : t) : t =
  let new_range = Code_range.extent_of_string destination (repr x) in
  { x with range = new_range }

let move_by ~(lines : int) ~(chars : int) (node : t) : (t, Error.t) result =
  let* shifted = Code_point.shift ~lines ~chars node.range.start in
  Ok (move_to shifted node)

let vernac_expr (x : t) =
  match x.kind with
  | Vernac ast -> Some (Coq.Ast.to_coq ast.v).v.expr
  | Comment -> None

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

let proof_with_tactic_of_raw_generic_tactic (env : Environ.env)
    (evd : Evd.evar_map) (raw_gen_tac : Gentactic.raw_generic_tactic) : string =
  Pp.string_of_ppcmds (Pputils.pr_raw_generic env evd raw_gen_tac)

[%%else]

let proof_with_tactic_of_raw_generic_tactic (env : Environ.env)
    (evd : Evd.evar_map) (raw_gen_tac : Gentactic.raw_generic_tactic) : string =
  Pp.string_of_ppcmds
    (Pputils.pr_raw_generic env evd (Gentactic.to_raw_genarg raw_gen_tac))

[%%endif]

let get_proof_with_tactic (x : t) : string option =
  match synpure_expr x with
  | Some (VernacProof (Some raw_arg, _)) ->
      let empty_env = Environ.empty_env in
      let empty_evd = Evd.empty in
      Some (proof_with_tactic_of_raw_generic_tactic empty_env empty_evd raw_arg)
  | _ -> None

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
  match x.kind with
  | Vernac ast -> (
      let coq_ast = Coq.Ast.to_coq ast.v in
      match coq_ast.v.expr with
      | VernacSynterp _ -> false
      | VernacSynPure expr -> (
          match expr with
          | Vernacexpr.VernacInstance _ ->
              let flags = coq_ast.v.attrs in
              List.exists
                (fun (flag : Attributes.vernac_flag) ->
                  let str, _ = flag.v in
                  String.equal str "program")
                flags
          | _ -> false))
  | Comment -> false

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

let get_ltac_command (x : t) : ltac_command option =
  Option.bind (get_tactic_raw_generic_arguments x) raw_arguments_to_ltac_command

let require_ltac_command (x : t) : (ltac_command, Error.t) result =
  match get_ltac_command x with
  | Some command -> Ok command
  | None ->
      Error.format_to_or_error
        "node %S isn't convertible to an ltac command (It probably isn't Ltac)"
        (repr x)

let get_goal_selector_opt (x : t) : Goal_select_view.t option =
  Option.bind
    (get_tactic_raw_generic_arguments x)
    raw_arguments_to_goal_selector

let get_raw_tactic_expr (x : t) : Ltac_plugin.Tacexpr.raw_tactic_expr option =
  Option.bind
    (get_tactic_raw_generic_arguments x)
    raw_arguments_to_raw_tactic_expr

let get_tacdef_bodies (x : t) : Ltac_plugin.Tacexpr.tacdef_body list option =
  Option.bind
    (get_tactic_raw_generic_arguments x)
    raw_arguments_to_tacdef_bodies

let require_raw_tactic_expr (x : t) :
    (Ltac_plugin.Tacexpr.raw_tactic_expr, Error.t) result =
  match get_tactic_raw_generic_arguments x with
  | Some args ->
      Option_utils.to_result
        (raw_arguments_to_raw_tactic_expr args)
        ~none:
          (Error.format_to_or_error
             "Could extract raw arguments from %s but not convert them to Ltac"
             (repr x))
  | None ->
      Error.format_to_or_error
        "%s isn't convertible to a raw_tactic_expr (It probably isn't Ltac)"
        (repr x)

let get_raw_tactic_expr_view (x : t) :
    Ltac_plugin.Tacexpr.r_dispatch Ltac_plugin.Tacexpr.gen_tactic_expr_r option
    =
  get_raw_tactic_expr x
  |> Option.map (fun (expr : Ltac_plugin.Tacexpr.raw_tactic_expr) -> expr.v)

let string_to_raw_tactic_expr (str : string) :
    (Ltac_plugin.Tacexpr.raw_tactic_expr, Error.t) result =
  let* node = syntax_node_of_string str Code_point.dummy in
  require_raw_tactic_expr node

let get_raw_atomic_tactic_expr (x : t) :
    Ltac_plugin.Tacexpr.raw_atomic_tactic_expr option =
  Option.bind (get_raw_tactic_expr x) Ltac.get_raw_atomic_tactic_expr

let coq_ast_of_ltac_command (command : Raw_gen_args_converter.ltac_command) :
    Coq.Ast.t =
  let args =
    Raw_gen_args_converter.ltac_command_to_raw_generic_arguments command
  in
  let expr_syn = Vernacexpr.VernacExtend (Ltac.ltac_tactic_extend_name, args) in
  let synterp_expr = Vernacexpr.VernacSynterp expr_syn in
  let control = mk_vernac_control synterp_expr in
  Coq.Ast.of_coq control

let coq_ast_of_ltac_raw_gen_args (ext : extend_name)
    (args : Genarg.raw_generic_argument list) : Coq.Ast.t option =
  match args with
  | [ _; _; _; _ ] ->
      let expr_syn = Vernacexpr.VernacExtend (ext, args) in
      let synterp_expr = Vernacexpr.VernacSynterp expr_syn in
      let control = mk_vernac_control synterp_expr in
      Some (Coq.Ast.of_coq control)
  | _ -> None

let ltac_command_to_syntax_node (command : Raw_gen_args_converter.ltac_command)
    (starting_point : Code_point.t) : t =
  let coq_ast = coq_ast_of_ltac_command command in
  of_coq_ast coq_ast starting_point

let ltac_command_to_syntax_node_in_state ~(token : Coq.Limits.Token.t)
    ~(st : Coq.State.t) (command : Raw_gen_args_converter.ltac_command)
    (starting_point : Code_point.t) : (t, Error.t) result =
  let coq_ast = coq_ast_of_ltac_command command in
  of_coq_ast_in_state ~token ~st coq_ast starting_point

let tactic_raw_generic_arguments_to_syntax_node (ext : extend_name)
    (args : Genarg.raw_generic_argument list) (starting_point : Code_point.t) :
    t option =
  match coq_ast_of_ltac_raw_gen_args ext args with
  | Some coq_ast -> Some (of_coq_ast coq_ast starting_point)
  | None -> None

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
    ?(selector : Goal_select_view.t option) ?(info_level : int option = None)
    ?(use_default = false) (starting_point : Code_point.t) : t =
  let cmd = { selector; info_level; raw_tactic_expr = raw_expr; use_default } in
  let tac = ltac_command_to_syntax_node cmd starting_point in
  tac

let raw_tactic_expr_to_syntax_node_in_state ~(token : Coq.Limits.Token.t)
    ~(st : Coq.State.t) (raw_expr : Ltac_plugin.Tacexpr.raw_tactic_expr)
    ?(selector : Goal_select_view.t option) ?(info_level = None)
    ?(use_default = false) (starting_point : Code_point.t) : (t, Error.t) result
    =
  let cmd = { selector; info_level; raw_tactic_expr = raw_expr; use_default } in
  ltac_command_to_syntax_node_in_state ~token ~st cmd starting_point

let drop_goal_selector (x : t) : t =
  match get_ltac_command x with
  | Some { info_level; raw_tactic_expr; use_default; _ } ->
      let args =
        { selector = None; info_level; raw_tactic_expr; use_default }
      in

      ltac_command_to_syntax_node args x.range.start |> inherit_metadata ~from:x
  | _ -> x

let add_goal_selector (x : t) (selector : Goal_select_view.t) :
    (t, Error.t) result =
  let* cmd = require_ltac_command x in
  match cmd.selector with
  | Some existing ->
      Error.format_to_or_error "%s already contains a goal selector: %s"
        (repr x)
        (Goal_select_view.to_string existing)
  | None ->
      let cmd = { cmd with selector = Some selector } in
      Ok
        (ltac_command_to_syntax_node cmd x.range.start
        |> inherit_metadata ~from:x)

let get_alias_kername (x : t) : Names.KerName.t option =
  Option.bind (get_raw_tactic_expr x) Ltac.get_alias_kername

let auto_alias_kername : Names.KerName.t option Lazy.t =
  lazy
    (match syntax_node_of_string "auto." Code_point.dummy with
    | Ok node -> get_alias_kername node
    | Error _ -> None)

let is_auto (x : t) : bool =
  match (get_alias_kername x, Lazy.force auto_alias_kername) with
  | Some actual, Some expected -> Names.KerName.equal actual expected
  | _ -> false

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
let syntax_node_list_to_raw_tactics (l : t list) :
    (Ltac_plugin.Tacexpr.raw_tactic_expr list, Error.t) result =
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
  let* raw_a = require_raw_tactic_expr a in

  let* raw_tactics_l = syntax_node_list_to_raw_tactics l in

  let args = get_tactic_raw_generic_arguments a in

  match args with
  | Some [ selector; info; _; use_default ] -> (
      let extend = Ltac.ltac_tactic_extend_name in

      let a_thens_l : Ltac_plugin.Tacexpr.raw_tactic_expr =
        CAst.make (Ltac_plugin.Tacexpr.TacThens (raw_a, raw_tactics_l))
      in

      let raw_arg =
        Raw_gen_args_converter.raw_generic_argument_of_raw_tactic_expr a_thens_l
      in
      let new_args = [ selector; info; raw_arg; use_default ] in

      match
        tactic_raw_generic_arguments_to_syntax_node extend new_args start_point
      with
      | Some node -> Ok node
      | None ->
          Error.format_to_or_error
            "failed to create a thens between %s and [%s]" (repr a)
            (l |> List.map repr |> String.concat "; "))
  | _ ->
      Error.string_to_or_error
        "Failed to extract the expected representation from raw generic \
         arguments"

let apply_tac_then (a : t) (b : t) ?(start_point : Code_point.t = a.range.start)
    () : (t, Error.t) result =
  let* command_a = require_ltac_command a in

  let* raw_b = require_raw_tactic_expr b in

  let a_then_b =
    Ltac_plugin.Tacexpr.TacThen (command_a.raw_tactic_expr, raw_b) |> CAst.make
  in

  let new_args =
    Raw_gen_args_converter.ltac_command_to_raw_generic_arguments
      { command_a with raw_tactic_expr = a_then_b }
  in

  tactic_raw_generic_arguments_to_syntax_node Ltac.ltac_tactic_extend_name
    new_args start_point
  |> Option.cata Result.ok
       (Error.format_to_or_error "failed to create a then betwen %s and %s"
          (repr a) (repr b))

let can_open_proof (x : t) : bool =
  is_proof_start x || is_definition_with_proof x
  || (is_instance_start x && not (is_program_instance_start x))
     (* TODO actually treat Program and Obligation *)
  || is_function_start x

let can_close_proof (x : t) : bool = is_proof_abort x || is_proof_end x

let is_proof_intro_or_end (x : t) : bool =
  is_proof_start x || is_proof_command x || is_proof_end x
