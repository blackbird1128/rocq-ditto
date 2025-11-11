open Sexplib.Std

type t = { line : int; character : int } [@@deriving sexp, yojson]

let pp (fmt : Format.formatter) (x : t) : unit =
  Format.fprintf fmt "(l: %d c: %d)" x.line x.character

let to_string (x : t) : string = Format.asprintf "%a" pp x

let code_point_from_lang_point (x : Lang.Point.t) : t =
  { line = x.line; character = x.character }
