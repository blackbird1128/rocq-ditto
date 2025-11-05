open Sexplib

type t =
  | String of string
  | Tag_sexp of string * Sexp.t * t
  | Tag_t of string * t
  | Of_sexp of Sexp.t
  | Of_exn of exn
  | Of_list of t list
[@@deriving sexp_of]

val of_string : string -> t
val of_exn : exn -> t
val of_sexp : Sexp.t -> t
val tag : t -> tag:string -> t
val tag_arg : t -> string -> 'a -> ('a -> Sexp.t) -> t
val tag_sexp : t -> string -> Sexp.t -> t
val combine : t list -> t

val tag_with_debug_infos :
  ?file:string -> ?funcname:string -> ?line:int -> t -> t

val to_string_hum : t -> string
val to_string_mach : t -> string
val pp : Format.formatter -> t -> unit

type 'a or_error = ('a, t) result

val of_result : ('a, string) result -> ('a, t) result
val to_string_result : t -> ('a, string) result
val or_error_to_string_result : 'a or_error -> ('a, string) result
val string_to_or_error : string -> ('a, t) result

val format_to_or_error :
  ('fmt, unit, string, ('payload, t) result) format4 -> 'fmt
