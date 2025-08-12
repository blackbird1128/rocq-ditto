type t = { line : int; character : int }

let pp (fmt : Format.formatter) (x : t) : unit =
  Format.fprintf fmt "(l: %d c: %d)" x.line x.character

let code_point_from_lang_point (x : Lang.Point.t) : t =
  { line = x.line; character = x.character }
