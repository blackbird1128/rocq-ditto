type t = { start : Code_point.t; end_ : Code_point.t }
[@@deriving sexp_of, to_yojson]

let make (start : Code_point.t) (end_ : Code_point.t) : (t, Error.t) result =
  if compare start end_ > 0 then
    Error.format_to_or_error "start: %s is bigger than end_: %s"
      (Code_point.to_string start)
      (Code_point.to_string end_)
  else Ok { start; end_ }

let pp (fmt : Format.formatter) (x : t) : unit =
  Format.fprintf fmt "{start_pos = %a; end_pos = %a}" Code_point.pp x.start
    Code_point.pp x.end_

let to_string (x : t) : string = Format.asprintf "%a" pp x

let equal (a : t) (b : t) : bool =
  Code_point.equal a.start b.start && Code_point.equal a.end_ b.end_

let compare (a : t) (b : t) : int =
  let c = Code_point.compare a.start b.start in
  if c <> 0 then c else Code_point.compare a.end_ b.end_

let is_empty (a : t) : bool = Code_point.compare a.start a.end_ = 0

let of_lang_range (x : Lang.Range.t) : t =
  {
    start = Code_point.of_lang_point x.start;
    end_ = Code_point.of_lang_point x.end_;
  }

let extent_of_string (starting_point : Code_point.t) (repr : string) : t =
  {
    start = starting_point;
    end_ = Code_point.advance_by_text starting_point repr;
  }

let are_colliding (a : t) (b : t) : bool =
  Code_point.lt (Code_point.max a.start b.start) (Code_point.min a.end_ b.end_)

let range_contains_other ~(container : t) (candidate : t) : bool =
  Code_point.compare container.start candidate.start <= 0
  && Code_point.compare candidate.end_ container.end_ <= 0

let of_yojson (json : Yojson.Safe.t) : (t, string) result =
  let ( let* ) = Result.bind in
  let* assoc =
    try Ok (Yojson.Safe.Util.to_assoc json)
    with Yojson.Safe.Util.Type_error _ ->
      Error "Invalid Json received in Code_range.of_yojson"
  in
  match assoc with
  | [ ("start", start_json); ("end_", end_json) ]
  | [ ("end_", end_json); ("start", start_json) ] ->
      let* start_point = Code_point.of_yojson start_json in
      let* end_point = Code_point.of_yojson end_json in
      make start_point end_point |> Result.map_error Error.to_string_hum
  | _ -> Error "Invalid Json received in Code_range.of_yojson"

let of_sexp (sexp : Sexplib.Sexp.t) : (t, Error.t) result =
  let ( let* ) = Result.bind in

  match sexp with
  | List [ List [ Atom "start"; start_sexp ]; List [ Atom "end_"; end_sexp ] ]
    ->
      let* start = Code_point.of_sexp start_sexp in
      let* end_ = Code_point.of_sexp end_sexp in
      make start end_
  | _ -> Error.string_to_or_error "Invalid S-exp received in Code_range.of_sexp"
