open Code_point

type t = { start : Code_point.t; end_ : Code_point.t }

let pp (fmt : Format.formatter) (x : t) : unit =
  Format.fprintf fmt "{start_pos = %a; end_pos = %a}" Code_point.pp x.start
    Code_point.pp x.end_

let to_string (x : t) : string = Format.asprintf "%a" pp x

let code_range_from_lang_range (x : Lang.Range.t) : t =
  {
    start = code_point_from_lang_point x.start;
    end_ = code_point_from_lang_point x.end_;
  }
