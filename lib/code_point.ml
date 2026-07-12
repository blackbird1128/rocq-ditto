open Sexplib.Std

type t = { line : int; character : int } [@@deriving sexp, yojson]

let dummy : t = { line = -1; character = -1 }

let pp (fmt : Format.formatter) (x : t) : unit =
  Format.fprintf fmt "(l: %d c: %d)" x.line x.character

let compare (a : t) (b : t) : int =
  let c = compare a.line b.line in
  if c = 0 then compare a.character b.character else c

let leq (a : t) (b : t) : bool = compare a b <= 0
let to_string (x : t) : string = Format.asprintf "%a" pp x

let shift (n_line : int) (n_char : int) (x : t) : t =
  { line = x.line + n_line; character = x.character + n_char }

let code_point_from_lang_point (x : Lang.Point.t) : t =
  { line = x.line; character = x.character }
