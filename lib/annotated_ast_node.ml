open Fleche

type annotatedASTNode = {
  ast : Doc.Node.Ast.t;
  range : Lang.Range.t;
  repr : string;
  id : int;
  proof_id : int option;
      (* the id of the proof associated with the node if there is one *)
}

let ast_node_to_yojson (ast_node : Doc.Node.Ast.t) : Yojson.Safe.t =
  `Assoc [ ("v", Lsp.JCoq.Ast.to_yojson ast_node.v); ("info", `Null) ]
(* TODO treat info *)

let ast_node_of_yojson (json : Yojson.Safe.t) : Doc.Node.Ast.t =
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

let to_yojson (node : annotatedASTNode) : Yojson.Safe.t =
  `Assoc
    [
      ("ast", ast_node_to_yojson node.ast);
      ("range", range_to_yojson node.range);
      ("repr", `String node.repr);
      ("id", `Int node.id);
      ("proof_id", match node.proof_id with Some id -> `Int id | None -> `Null);
    ]

let of_yojson (json : Yojson.Safe.t) : annotatedASTNode =
  let open Yojson.Safe.Util in
  {
    ast = json |> member "ast" |> ast_node_of_yojson;
    range = json |> member "range" |> range_of_yojson;
    repr = json |> member "repr" |> to_string;
    id = json |> member "id" |> to_int;
    proof_id = json |> member "proof_id" |> to_option to_int;
  }

let shift_point (n_line : int) (n_char : int) (x : Lang.Point.t) : Lang.Point.t
    =
  { x with line = x.line + n_line; offset = x.offset + n_char }

let shift_node (n_line : int) (n_char : int) (x : annotatedASTNode) :
    annotatedASTNode =
  {
    x with
    range =
      {
        start = shift_point n_line n_char x.range.start;
        end_ = shift_point n_line n_char x.range.end_;
      };
  }

let is_doc_node_ast_tactic (x : annotatedASTNode) : bool =
  match (Coq.Ast.to_coq x.ast.v).CAst.v.expr with
  | VernacSynterp synterp_expr -> (
      match synterp_expr with
      | VernacExtend (ext, _) ->
          if ext.ext_plugin = "coq-core.plugins.ltac" then true else false
      | _ -> false)
  | VernacSynPure _ -> false

let is_doc_node_ast_proof_start (x : annotatedASTNode) : bool =
  match (Coq.Ast.to_coq x.ast.v).CAst.v.expr with
  | VernacSynterp _ -> false
  | VernacSynPure expr -> (
      match expr with
      | Vernacexpr.VernacStartTheoremProof _ -> true
      | _ -> false)

let is_doc_node_ast_proof_end (x : annotatedASTNode) : bool =
  match (Coq.Ast.to_coq x.ast.v).CAst.v.expr with
  | VernacSynterp _ -> false
  | VernacSynPure expr -> (
      match expr with Vernacexpr.VernacEndProof _ -> true | _ -> false)

let is_doc_node_ast_proof_command (x : annotatedASTNode) : bool =
  match (Coq.Ast.to_coq x.ast.v).CAst.v.expr with
  | VernacSynterp _ -> false
  | VernacSynPure expr -> (
      match expr with Vernacexpr.VernacProof _ -> true | _ -> false)
