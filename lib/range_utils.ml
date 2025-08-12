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

let range_from_starting_point_and_repr (starting_point : Code_point.t)
    (repr : string) : Code_range.t =
  let number_line_jump =
    String.fold_left
      (fun count char -> if char = '\n' then count + 1 else count)
      0 repr
  in
  let last_jump = String.rindex_opt repr '\n' in
  let offset_length = String.length repr in
  {
    start = starting_point;
    end_ =
      {
        line = starting_point.line + number_line_jump;
        character =
          (if number_line_jump > 0 then
             String.length repr - Option.get last_jump - 1
           else starting_point.character + offset_length);
      };
  }

let are_flat_ranges_colliding (a : int * int) (b : int * int) : bool =
  let a_start, a_end = a in
  let b_start, b_end = b in
  not (a_end < b_start || b_end < a_start)

let common_range (a : int * int) (b : int * int) : (int * int) option =
  let a_start, a_end = a in
  let b_start, b_end = b in
  if are_flat_ranges_colliding (a_start, a_end) (b_start, b_end) then
    Some (max a_start b_start, min a_end b_end)
  else None
