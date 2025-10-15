type t = { start : Code_point.t; end_ : Code_point.t } [@@deriving sexp, yojson]

val pp : Format.formatter -> t -> unit
val to_string : t -> string
val code_range_from_lang_range : Lang.Range.t -> t
