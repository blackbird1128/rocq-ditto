type position = { line : int; character : int; offset : int } [@@deriving show]
type range = { start : position; end_ : position } [@@deriving show]
type rangedSpan = { range : range; span : CoqAst.t option }
type rangedCoqSpan = { range : range; span : Vernacexpr.vernac_control option }

type completionStatus = { status : string list; range : range }
[@@deriving show]

type lspDocument = { spans : rangedSpan list; completed : completionStatus }
type coqDocument = { spans : rangedCoqSpan list; completed : completionStatus }

(* Parse a position object *)
let parse_position (json : Yojson.Safe.t) : position =
  let open Yojson.Safe.Util in
  {
    line = json |> member "line" |> to_int;
    character = json |> member "character" |> to_int;
    offset = json |> member "offset" |> to_int;
  }

(* Parse a range object *)
let parse_range (json : Yojson.Safe.t) : range =
  let open Yojson.Safe.Util in
  {
    start = json |> member "start" |> parse_position;
    end_ = json |> member "end" |> parse_position;
  }

(* Parse a rangedSpan object *)
let parse_rangedSpan (json : Yojson.Safe.t) : rangedSpan =
  let open Yojson.Safe.Util in
  let span_result = json |> member "span" |> CoqAst.of_yojson in
  {
    range = json |> member "range" |> parse_range;
    span =
      (if Result.is_ok span_result then Some (Result.get_ok span_result)
       else None);
  }

(* Parse a completionStatus object *)
let parse_completionStatus (json : Yojson.Safe.t) : completionStatus =
  let open Yojson.Safe.Util in
  {
    status = json |> member "status" |> to_list |> List.map to_string;
    range = json |> member "range" |> parse_range;
  }

(* Parse the main document object *)
let parse_document (json : Yojson.Safe.t) : lspDocument =
  let open Yojson.Safe.Util in
  {
    spans = json |> member "spans" |> to_list |> List.map parse_rangedSpan;
    completed = json |> member "completed" |> parse_completionStatus;
  }

let ranged_span_to_ranged_coq_span (x : rangedSpan) : rangedCoqSpan =
  { span = Option.map Coq.Ast.to_coq x.span; range = x.range }

let lsp_doc_to_coq_doc (doc : lspDocument) : coqDocument =
  let coq_spans =
    List.map (fun x -> ranged_span_to_ranged_coq_span x) doc.spans
  in
  { spans = coq_spans; completed = doc.completed }
