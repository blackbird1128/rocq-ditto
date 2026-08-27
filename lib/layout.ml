let prefix_before (first_point : Code_point.t) : string =
  String.concat ""
    [ String.make first_point.line '\n'; String.make first_point.character ' ' ]

let gap_between (first_range : Code_range.t) (second_range : Code_range.t) :
    (string, Error.t) result =
  let line_diff = second_range.start.line - first_range.end_.line in
  if line_diff < 0 then
    Error.format_to_or_error
      "second range starts before previous ends (line)\n\
       first range=%s\n\
       second range=%s"
      (Code_range.to_string first_range)
      (Code_range.to_string second_range)
  else if line_diff = 0 then
    let char_diff = second_range.start.character - first_range.end_.character in
    if char_diff < 0 then
      Error.format_to_or_error
        "second range starts before previous ends (char)\n\
         first range=%s\n\
         second range=%s"
        (Code_range.to_string first_range)
        (Code_range.to_string second_range)
    else Ok (String.make char_diff ' ')
  else
    Ok
      (String.concat ""
         [
           String.make line_diff '\n';
           String.make second_range.start.character ' ';
         ])
