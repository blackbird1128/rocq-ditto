open Sexplib.Std

type t = { line : int; character : int } [@@deriving sexp_of, to_yojson]

let make (line : int) (character : int) : (t, Error.t) result =
  if line < 0 then
    Error.format_to_or_error "Can't create a point (%d,%d) with a negative line"
      line character
  else if character < 0 then
    Error.format_to_or_error
      "Can't create a point (%d,%d) with a negative character" line character
  else Ok { line; character }

let dummy : t = { line = -1; character = -1 }
let origin : t = { line = 0; character = 0 }

let pp (fmt : Format.formatter) (x : t) : unit =
  Format.fprintf fmt "(l: %d c: %d)" x.line x.character

let equal (a : t) (b : t) : bool = a.line = b.line && a.character = b.character

let compare (a : t) (b : t) : int =
  let c = Int.compare a.line b.line in
  if c = 0 then Int.compare a.character b.character else c

let leq (a : t) (b : t) : bool = compare a b <= 0
let to_string (x : t) : string = Format.asprintf "%a" pp x

let shift ~(lines : int) ~(chars : int) (x : t) : (t, Error.t) result =
  make (x.line + lines) (x.character + chars)

let of_lang_point (x : Lang.Point.t) : t =
  { line = x.line; character = x.character }

let advance_by_text (x : t) (str : string) : t =
  let number_line_jump =
    String.fold_left
      (fun count char -> if char = '\n' then count + 1 else count)
      0 str
  in
  let last_jump = String.rindex_opt str '\n' in
  let offset_length = String.length str in
  {
    line = x.line + number_line_jump;
    character =
      (if number_line_jump > 0 then String.length str - Option.get last_jump - 1
       else x.character + offset_length);
  }

let of_yojson (json : Yojson.Safe.t) : (t, string) result =
  let ( let* ) = Result.bind in
  let* assoc =
    try Ok (Yojson.Safe.Util.to_assoc json)
    with Yojson.Safe.Util.Type_error _ ->
      Error "Invalid Json received in Code_point.of_yojson"
  in
  match assoc with
  | [ ("line", `Int line); ("character", `Int character) ]
  | [ ("character", `Int character); ("line", `Int line) ] ->
      make line character |> Result.map_error Error.to_string_hum
  | _ -> Error "Invalid Json received in Code_point.of_yojson"

let int_of_string_err (arg : string) : (int, Error.t) result =
  match int_of_string_opt arg with
  | Some integer -> Ok integer
  | None ->
      Error.format_to_or_error
        "given string %S is not a valid representation of an integer" arg

let of_sexp (sexp : Sexplib.Sexp.t) : (t, Error.t) result =
  let ( let* ) = Result.bind in

  match sexp with
  | List
      [
        List [ Atom "line"; Atom line_str ];
        List [ Atom "character"; Atom character_str ];
      ] ->
      let* line = int_of_string_err line_str in
      let* character = int_of_string_err character_str in
      make line character
  | _ -> Error.string_to_or_error "Invalid S-exp received in Code_point.of_sexp"
