type t = { line : int; character : int } [@@deriving sexp, yojson]

val origin : t
(** The origin point (0, 0) *)

val dummy : t
(** An invalid point for operations that require a position but do not use it.
    Its coordinates are deliberately unspecified; callers must not inspect or
    reproduce them. *)

val pp : Format.formatter -> t -> unit
val equal : t -> t -> bool
val compare : t -> t -> int
val leq : t -> t -> bool
val shift : lines:int -> chars:int -> t -> t
val to_string : t -> string
val of_lang_point : Lang.Point.t -> t
