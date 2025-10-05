open Sexplib
open Sexplib.Std

type t =
  | String of string
  | Tag_sexp of string * Sexp.t * t
  | Tag_t of string * t
  | Of_sexp of Sexp.t
  | Of_exn of exn
[@@deriving sexp_of]

let of_string (s : string) = String s
let of_exn (exn : exn) = Of_exn exn
let tag (t : t) ~(tag : string) = Tag_t (tag, t)

let[@inline] tag_with_debug_infos ?(file = __FILE__) ?(funcname = __FUNCTION__)
    ?(line = __LINE__) (t : t) =
  let loc =
    Format.sprintf "File: %s, function: %s, line: %d" file funcname line
  in

  tag t ~tag:loc

let tag_arg (t : t) (tag : string) (arg : 'a) (sexp_of_arg : 'a -> Sexp.t) : t =
  let sexp = sexp_of_arg arg in
  Tag_sexp (tag, sexp, t)

let to_string_hum (t : t) : string =
  let rec render = function
    | String s -> s
    | Tag_sexp (tag, sexp, t) ->
        tag ^ ": " ^ Sexp.to_string_hum sexp ^ "\n" ^ render t
    | Tag_t (tag, t) -> tag ^ "\n" ^ render t
    | Of_sexp sexp -> Sexp.to_string_hum ~indent:2 sexp
    | Of_exn exn -> Printexc.to_string exn
  in
  render t

let to_string_mach (t : t) : string = Sexp.to_string (sexp_of_t t)

let pp (fmt : Format.formatter) (t : t) =
  Format.fprintf fmt "%s" (to_string_hum t)

type 'a or_error = ('a, t) result

let of_result = function Ok x -> Ok x | Error s -> Error (of_string s)
let to_string_result (t : t) = Error (to_string_hum t)

let or_error_to_string_result (x : 'a or_error) =
  match x with Ok a -> Ok a | Error t -> to_string_result t

let string_to_or_error_err (x : string) : ('a, 't) result = Error (of_string x)
