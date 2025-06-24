open Sexplib
open Sexplib.Std

type t =
  | String of string
  | Tag_sexp of string * Sexp.t
  | Tag_t of string * t
  | Of_sexp of Sexp.t
  | Of_exn of exn
[@@deriving sexp_of]

val of_string : string -> t
val of_exn : exn -> t
val tag : t -> tag:string -> t
val tag_arg : string -> 'a -> ('a -> Sexp.t) -> t
val create : string -> 'a -> ('a -> Sexp.t) -> t
val create_s : string -> Sexp.t -> t
val to_string_hum : t -> string
val to_string_mach : t -> string
val pp : Format.formatter -> t -> unit

type 'a or_error = ('a, t) result

val of_result : ('a, string) result -> ('a, t) result
