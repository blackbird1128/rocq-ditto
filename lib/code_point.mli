type t = private { line : int; character : int } [@@deriving sexp_of, to_yojson]

val make : int -> int -> (t, Error.t) result

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
val shift : lines:int -> chars:int -> t -> (t, Error.t) result
val to_string : t -> string
val of_lang_point : Lang.Point.t -> t
val advance_by_text : t -> string -> t
val of_yojson : Yojson.Safe.t -> (t, string) result
val of_sexp : Sexplib.Sexp.t -> (t, Error.t) result
