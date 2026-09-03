open Code_point

type t = { start : Code_point.t; end_ : Code_point.t } [@@deriving sexp, yojson]

let pp (fmt : Format.formatter) (x : t) : unit =
  Format.fprintf fmt "{start_pos = %a; end_pos = %a}" Code_point.pp x.start
    Code_point.pp x.end_

let to_string (x : t) : string = Format.asprintf "%a" pp x

let equal (a : t) (b : t) : bool =
  Code_point.equal a.start b.start && Code_point.equal a.end_ b.end_

let compare (a : t) (b : t) : int =
  let c = Code_point.compare a.start b.start in
  if c <> 0 then c else Code_point.compare a.end_ b.end_

let of_lang_range (x : Lang.Range.t) : t =
  { start = of_lang_point x.start; end_ = of_lang_point x.end_ }

let extent_of_string (starting_point : Code_point.t) (repr : string) : t =
  {
    start = starting_point;
    end_ = Code_point.move_throught_text starting_point repr;
  }

let are_flat_ranges_colliding (a : int * int) (b : int * int) : bool =
  let a_start, a_end = a in
  let b_start, b_end = b in
  not (a_end <= b_start || b_end <= a_start)
(* half open intervals *)

(* as a code range is half_open (the end is open [a,b] and [b,c] are not colliding, this also mean that a node finishing on the character 0 of a line isn't included in this line  *)
let line_span (r : t) : int * int =
  let end_excl =
    if r.end_.character = 0 then r.end_.line else r.end_.line + 1
  in
  (r.start.line, end_excl)

let char_span_on_line (r : t) (line : int) : int * int =
  (* half-open char span [start_char, end_char) of r on a particular line that r touches *)
  let start_char = if r.start.line < line then 0 else r.start.character in
  let _, end_line_excl = line_span r in
  let end_char =
    if end_line_excl > line + 1 then max_int else r.end_.character
  in
  (start_char, end_char)

let are_colliding (a : t) (b : t) : bool =
  let a_ls, a_le = line_span a in
  let b_ls, b_le = line_span b in
  (* common line span [cs, ce) *)
  let cs = max a_ls b_ls in
  let ce = min a_le b_le in
  if ce <= cs then false
  else if ce - cs >= 2 then true
  else
    let line = cs in
    let a_cs = char_span_on_line a line in
    let b_cs = char_span_on_line b line in
    are_flat_ranges_colliding a_cs b_cs

let range_contains_other ~(container : t) (candidate : t) : bool =
  Code_point.compare container.start candidate.start <= 0
  && Code_point.compare candidate.end_ container.end_ <= 0
