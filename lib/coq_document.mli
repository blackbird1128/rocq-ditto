type position = { line : int; character : int; offset : int } [@@deriving show]
type range = { start : position; end_ : position } [@@deriving show]
type rangedSpan = { range : range; span : Coq_ast.t option }
type rangedCoqSpan = { range : range; span : Vernacexpr.vernac_control option }

type completionStatus = { status : string list; range : range }
[@@deriving show]

type lspDocument = { spans : rangedSpan list; completed : completionStatus }
type coqDocument = { spans : rangedCoqSpan list; completed : completionStatus }

val parse_position : json:Yojson.Safe.t -> position
val parse_position : Yojson.Safe.t -> position
val parse_range : Yojson.Safe.t -> range
val parse_rangedSpan : Yojson.Safe.t -> rangedSpan
val parse_completionStatus : Yojson.Safe.t -> completionStatus
val parse_document : Yojson.Safe.t -> lspDocument
val ranged_span_to_ranged_coq_span : rangedSpan -> rangedCoqSpan
val lsp_doc_to_coq_doc : lspDocument -> coqDocument
