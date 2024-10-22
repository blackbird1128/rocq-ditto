
type position = {
  line : int;
  character : int;
  offset : int;
} [@@deriving show]

type range = {
    start: position;
    end_: position;
} [@@deriving show]


type rangedSpan = {
  range: range;
  span: CoqAst.t option;

}

type completionStatus = {

    status: string list;
    range: range;
} [@@deriving show]

type document = {
    spans: rangedSpan list;
    completed: completionStatus
} 


val parse_position: json : Yojson.Safe.t -> position

val parse_position : Yojson.Safe.t -> position

val parse_range : Yojson.Safe.t -> range

val parse_rangedSpan : Yojson.Safe.t -> rangedSpan

val parse_completionStatus : Yojson.Safe.t -> completionStatus

val parse_document : Yojson.Safe.t -> document

