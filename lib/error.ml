open Sexplib
open Sexplib.Std

type t =
  | String of string
  | Tag_sexp of string * Sexp.t * t
  | Tag_t of string * t
  | Of_sexp of Sexp.t
  | Of_exn of exn
  | Of_list of t list
[@@deriving sexp_of]

let of_sexp (s : Sexp.t) : t = Of_sexp s
let of_string (s : string) : t = String s
let of_exn (exn : exn) : t = Of_exn exn
let tag (t : t) ~(tag : string) : t = Tag_t (tag, t)

let combine (errs : t list) : t =
  match errs with [] -> String "no error" | [ e ] -> e | lst -> Of_list lst

let tag_with_debug_infos ~(pos : Lexing.position) (t : t) =
  let loc =
    Format.sprintf "File: %s, line: %d, char: %d" pos.pos_fname pos.pos_lnum
      pos.pos_bol
  in

  tag t ~tag:loc

let tag_arg (e : t) ~(tag : string) (arg : 'a) (sexp_of_arg : 'a -> Sexp.t) : t
    =
  let sexp = sexp_of_arg arg in
  Tag_sexp (tag, sexp, e)

let tag_sexp (e : t) ~(tag : string) (arg : Sexplib.Sexp.t) : t =
  Tag_sexp (tag, arg, e)

let pp (fmt : Format.formatter) (e : t) =
  let rec aux indent fmt = function
    | String s -> Format.fprintf fmt "%s%s" (String.make indent ' ') s
    | Tag_t (tag, t) ->
        Format.fprintf fmt "%s%s:@\n%a" (String.make indent ' ') tag
          (aux (indent + 2))
          t
    | Tag_sexp (tag, sexp, t) ->
        Format.fprintf fmt "%s%s: %s@\n%a" (String.make indent ' ') tag
          (Sexp.to_string_hum sexp)
          (aux (indent + 2))
          t
    | Of_exn exn ->
        Format.fprintf fmt "%s%s" (String.make indent ' ')
          (Printexc.to_string exn)
    | Of_sexp sexp ->
        Format.fprintf fmt "%s%s" (String.make indent ' ')
          (Sexp.to_string_hum sexp)
    | Of_list l ->
        List.iteri
          (fun i e ->
            Format.fprintf fmt "%s- [%d]@\n%a" (String.make indent ' ') i
              (aux (indent + 2))
              e)
          l
  in
  aux 0 fmt e

let to_string_hum (e : t) : string = Format.asprintf "%a" pp e
let to_string_mach (e : t) : string = Sexp.to_string (sexp_of_t e)

type 'a or_error = ('a, t) result

let of_result = function Ok x -> Ok x | Error s -> Error (of_string s)
let to_string_result (t : t) : ('a, string) result = Error (to_string_hum t)

let or_error_to_string_result (x : 'a or_error) : ('a, string) result =
  match x with Ok a -> Ok a | Error t -> to_string_result t

let string_to_or_error (x : string) : ('a, t) result = Error (of_string x)

let format_to_or_error fmt =
  Stdlib.Format.kasprintf (fun s -> Error (of_string s)) fmt

let protect_to_result (r : ('a, 'b) Coq.Protect.E.t) : ('a, t) result =
  match r with
  | { r = Interrupted; feedback = _ } -> string_to_or_error "Interrupted"
  | { r = Completed (Error (User { msg; _ })); feedback = _ } ->
      string_to_or_error (Pp.string_of_ppcmds msg)
  | { r = Completed (Error (Anomaly { msg; _ })); feedback = _ } ->
      string_to_or_error ("Anomaly " ^ Pp.string_of_ppcmds msg)
  | { r = Completed (Ok r); feedback = _ } -> Ok r

let protect_to_result_with_feedback (r : ('a, 'b) Coq.Protect.E.t) :
    ('a * 'b Coq.Message.t list, t * 'b Coq.Message.t list) result =
  match r with
  | { r = Interrupted; feedback } -> Error (of_string "Interrupted", feedback)
  | { r = Completed (Error (User { msg; _ })); feedback } ->
      Error (of_string (Pp.string_of_ppcmds msg), feedback)
  | { r = Completed (Error (Anomaly { msg; _ })); feedback } ->
      Error (of_string ("Anomaly " ^ Pp.string_of_ppcmds msg), feedback)
  | { r = Completed (Ok r); feedback } -> Ok (r, feedback)
