open Fleche

type syntaxNode = {
  ast : Doc.Node.Ast.t option;
  range : Lang.Range.t;
  repr : string;
  id : int;
  proof_id : int option;
      (* the id of the proof associated with the node if there is one *)
}

let pp_doc_ast (fmt : Format.formatter) (ast : Doc.Node.Ast.t) : unit =
  Pp.pp_with fmt (Coq.Ast.print ast.v)

let pp_syntax_node (fmt : Format.formatter) (node : syntaxNode) : unit =
  Format.fprintf fmt "{@ ";
  Format.fprintf fmt "ast: %a@ "
    (fun fmt ast -> Format.pp_print_option pp_doc_ast fmt ast)
    node.ast;
  Format.fprintf fmt "range: %a@ " Lang.Range.pp node.range;
  Format.fprintf fmt "repr: %s@ " node.repr;
  Format.fprintf fmt "id: %d@ " node.id;
  Format.fprintf fmt "proof id: %a@ "
    (fun fmt id -> Format.pp_print_option Format.pp_print_int fmt id)
    node.proof_id;
  Format.fprintf fmt "}"

let generate_ast code =
  print_endline ("Code : " ^ code);
  let mode = Ltac_plugin.G_ltac.classic_proof_mode in
  let entry = Pvernac.main_entry (Some mode) in
  let code_stream = Gramlib.Stream.of_string code in
  let init_parser = Pcoq.Parsable.make code_stream in
  let rec f parser =
    match Pcoq.Entry.parse entry parser with
    | None -> []
    | Some ast -> ast :: f parser
  in
  f init_parser

let syntax_node_of_string (code : string) (range : Lang.Range.t) :
    (syntaxNode, string) result =
  if String.length code > range.end_.offset - range.start.offset then
    Error
      "Incorrect range: range end offset minus range start offset smaller than \
       node character size"
  else if
    range.start.line = range.end_.line
    && String.length code > range.end_.character - range.start.character
  then
    Error
      "Incorrect range: range end character minus range start character \
       smaller than node character size"
  else
    match generate_ast code with
    | [] -> Error ("no node found in string " ^ code)
    | [ x ] ->
        let node_ast : Doc.Node.Ast.t =
          { v = Coq.Ast.of_coq x; ast_info = None }
        in

        Ok
          {
            ast = Some node_ast;
            range;
            id = 0;
            (*id is set during insertion in a document*)
            repr = code;
            proof_id = None;
          }
    | _ -> Error ("more than one node found in string " ^ code)

let nodes_of_string (code : string) (ranges : Lang.Range.t list) :
    (syntaxNode list, string) result =
  match generate_ast code with
  | [] -> Ok []
  | l ->
      let length_l = List.length l in
      let num_ranges = List.length ranges in

      if length_l != num_ranges then
        Error
          (Printf.sprintf
             "The number of generated AST nodes (%d) does not match the number \
              of provided ranges (%d)."
             length_l num_ranges)
      else
        Ok
          (List.map2
             (fun x range ->
               let node_ast : Doc.Node.Ast.t =
                 { v = Coq.Ast.of_coq x; ast_info = None }
               in

               {
                 ast = Some node_ast;
                 range;
                 id = 0;
                 (* id is set during document insertion *)
                 repr = code;
                 proof_id = None;
               })
             l ranges)

let syntax_node_of_coq_ast (ast : Coq.Ast.t) (range : Lang.Range.t) : syntaxNode
    =
  let node_ast : Doc.Node.Ast.t = { v = ast; ast_info = None } in
  {
    ast = Some node_ast;
    range;
    id = 0;
    (* id is set during document insertion *)
    repr = Ppvernac.pr_vernac (Coq.Ast.to_coq ast) |> Pp.string_of_ppcmds;
    proof_id = None;
  }

let qed_ast_node (range : Lang.Range.t) : syntaxNode =
  Result.get_ok (syntax_node_of_string "Qed." range)

let syntax_node_to_yojson (ast_node : Doc.Node.Ast.t) : Yojson.Safe.t =
  `Assoc [ ("v", Lsp.JCoq.Ast.to_yojson ast_node.v); ("info", `Null) ]
(* TODO treat info *)

let syntax_node_of_yojson (json : Yojson.Safe.t) : Doc.Node.Ast.t =
  let open Yojson.Safe.Util in
  {
    v = json |> member "v" |> Lsp.JCoq.Ast.of_yojson |> Result.get_ok;
    ast_info = None;
  }
(* TODO treat AST info *)

let point_to_yojson (point : Lang.Point.t) : Yojson.Safe.t =
  `Assoc
    [
      ("line", `Int point.line);
      ("character", `Int point.character);
      ("offset", `Int point.offset);
    ]

let point_of_yojson (json : Yojson.Safe.t) : Lang.Point.t =
  let open Yojson.Safe.Util in
  {
    line = json |> member "line" |> to_int;
    character = json |> member "character" |> to_int;
    offset = json |> member "offset" |> to_int;
  }

let range_to_yojson (range : Lang.Range.t) : Yojson.Safe.t =
  `Assoc
    [
      ("start", point_to_yojson range.start);
      ("end_", point_to_yojson range.end_);
    ]

let range_of_yojson (json : Yojson.Safe.t) : Lang.Range.t =
  let open Yojson.Safe.Util in
  {
    start = json |> member "start" |> point_of_yojson;
    end_ = json |> member "end_" |> point_of_yojson;
  }

let to_yojson (node : syntaxNode) : Yojson.Safe.t =
  `Assoc
    [
      ( "ast",
        match node.ast with
        | Some ast -> syntax_node_to_yojson ast
        | None -> `Null );
      ("range", range_to_yojson node.range);
      ("repr", `String node.repr);
      ("id", `Int node.id);
      ("proof_id", match node.proof_id with Some id -> `Int id | None -> `Null);
    ]

let of_yojson (json : Yojson.Safe.t) : syntaxNode =
  let open Yojson.Safe.Util in
  {
    ast = json |> member "ast" |> to_option syntax_node_of_yojson;
    range = json |> member "range" |> range_of_yojson;
    repr = json |> member "repr" |> to_string;
    id = json |> member "id" |> to_int;
    proof_id = json |> member "proof_id" |> to_option to_int;
  }

let shift_point (n_line : int) (n_char : int) (n_offset : int)
    (x : Lang.Point.t) : Lang.Point.t =
  {
    line = x.line + n_line;
    character = x.character + n_char;
    offset = x.offset + n_char + n_offset;
  }

let shift_range (n_line : int) (n_char : int) (n_offset : int)
    (x : Lang.Range.t) : Lang.Range.t =
  {
    start = shift_point n_line n_char n_offset x.start;
    end_ = shift_point n_line n_char n_offset x.end_;
  }

let shift_node (n_line : int) (n_char : int) (n_offset : int) (x : syntaxNode) :
    syntaxNode =
  { x with range = shift_range n_line n_char n_offset x.range }

let is_doc_node_ast_tactic (x : syntaxNode) : bool =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).CAst.v.expr with
      | VernacSynterp synterp_expr -> (
          match synterp_expr with
          | VernacExtend (ext, _) ->
              if ext.ext_plugin = "coq-core.plugins.ltac" then true else false
          | _ -> false)
      | VernacSynPure _ -> false)
  | None -> false

let is_doc_node_ast_proof_command (x : syntaxNode) : bool =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).CAst.v.expr with
      | VernacSynterp _ -> false
      | VernacSynPure expr -> (
          match expr with Vernacexpr.VernacProof _ -> true | _ -> false))
  | None -> false

let is_doc_node_goal_start (x : syntaxNode) : bool =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).CAst.v.expr with
      | VernacSynterp _ -> false
      | VernacSynPure expr -> (
          match expr with
          | Vernacexpr.VernacDefinition
              ((discharge, object_kind), name_decl, definition_expr) -> (
              match definition_expr with ProveBody _ -> true | _ -> false)
          | _ -> false))
  | None -> false

let is_doc_node_ast_proof_start (x : syntaxNode) : bool =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).CAst.v.expr with
      | VernacSynterp _ -> false
      | VernacSynPure expr -> (
          match expr with
          | Vernacexpr.VernacStartTheoremProof _ -> true
          | _ -> false))
  | None -> false

let is_doc_node_ast_proof_end (x : syntaxNode) : bool =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).CAst.v.expr with
      | VernacSynterp _ -> false
      | VernacSynPure expr -> (
          match expr with Vernacexpr.VernacEndProof _ -> true | _ -> false))
  | None -> false

let is_doc_node_ast_proof_abort (x : syntaxNode) : bool =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).CAst.v.expr with
      | VernacSynterp _ -> false
      | VernacSynPure expr -> (
          match expr with
          | Vernacexpr.VernacAbort -> true
          | Vernacexpr.VernacAbortAll ->
              true
              (*not sure what is the fundamental difference between abort and abort all *)
          | _ -> false))
  | None -> false

let node_can_open_proof (x : syntaxNode) : bool =
  is_doc_node_ast_proof_start x || is_doc_node_goal_start x

let node_can_close_proof (x : syntaxNode) : bool =
  is_doc_node_ast_proof_abort x || is_doc_node_ast_proof_end x

let is_doc_node_proof_intro_or_end (x : syntaxNode) : bool =
  is_doc_node_ast_proof_start x
  || is_doc_node_ast_proof_command x
  || is_doc_node_ast_proof_end x
