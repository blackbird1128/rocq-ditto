open Sexplib.Std

type t = { line : int; character : int } [@@deriving sexp, yojson]

let dummy : t = { line = -1; character = -1 }
let origin : t = { line = 0; character = 0 }

let pp (fmt : Format.formatter) (x : t) : unit =
  Format.fprintf fmt "(l: %d c: %d)" x.line x.character

let equal (a : t) (b : t) : bool = a.line = b.line && a.character = b.character

let compare (a : t) (b : t) : int =
  let c = Int.compare a.line b.line in
  if c = 0 then Int.compare a.character b.character else c

let leq (a : t) (b : t) : bool = compare a b <= 0
let to_string (x : t) : string = Format.asprintf "%a" pp x

let shift ~(lines : int) ~(chars : int) (x : t) : t =
  { line = x.line + lines; character = x.character + chars }

let of_lang_point (x : Lang.Point.t) : t =
  { line = x.line; character = x.character }
