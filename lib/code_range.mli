type t = private { start : Code_point.t; end_ : Code_point.t }
[@@deriving sexp, yojson]

val make : Code_point.t -> Code_point.t -> (t, Error.t) result
val pp : Format.formatter -> t -> unit
val to_string : t -> string
val equal : t -> t -> bool
val compare : t -> t -> int
val of_lang_range : Lang.Range.t -> t
val extent_of_string : Code_point.t -> string -> t
val are_flat_ranges_colliding : int * int -> int * int -> bool
val are_colliding : t -> t -> bool
val range_contains_other : container:t -> t -> bool
