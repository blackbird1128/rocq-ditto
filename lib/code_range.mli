open Code_point

type t = { start : Code_point.t; end_ : Code_point.t }

val pp : Format.formatter -> t -> unit
val to_string : t -> string
val code_range_from_lang_range : Lang.Range.t -> t
