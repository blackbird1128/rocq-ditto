type t = { line : int; character : int } [@@deriving sexp, yojson]

val pp : Format.formatter -> t -> unit
val compare : t -> t -> int
val leq : t -> t -> bool
val shift : int -> int -> t -> t
val to_string : t -> string
val code_point_from_lang_point : Lang.Point.t -> t
