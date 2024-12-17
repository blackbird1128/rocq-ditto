let push_range_n_char (n_char : int) (range : Lang.Range.t) : Lang.Range.t =
  let new_start =
    {
      range.start with
      character = range.start.character + n_char;
      offset = range.start.offset + n_char;
    }
  in
  let new_end =
    {
      range.end_ with
      character = range.end_.character + n_char;
      offset = range.end_.offset + n_char;
    }
  in
  { start = new_start; end_ = new_end }
