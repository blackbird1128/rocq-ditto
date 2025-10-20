let error_location_to_string (location : Lang.Range.t) : string =
  if location.start.line = location.end_.line then
    "line "
    ^ string_of_int location.start.line
    ^ ", characters: "
    ^ string_of_int location.start.character
    ^ "-"
    ^ string_of_int location.end_.character
  else
    "line "
    ^ string_of_int location.start.line
    ^ "-"
    ^ string_of_int location.end_.line
    ^ ", characters: "
    ^ string_of_int location.start.character
    ^ "-"
    ^ string_of_int location.end_.character

let diagnostic_kind_to_str (diag_kind : Lang.Diagnostic.Severity.t) : string =
  if diag_kind = Lang.Diagnostic.Severity.error then "Error"
  else if diag_kind = Lang.Diagnostic.Severity.hint then "Hint"
  else if diag_kind = Lang.Diagnostic.Severity.information then "Information"
  else "Warning"

let pp_diagnostic (fmt : Format.formatter) (diag : Lang.Diagnostic.t) : unit =
  Format.fprintf fmt "At: %s %s: %s"
    (error_location_to_string diag.range)
    (diagnostic_kind_to_str diag.severity)
    (Pp.string_of_ppcmds diag.message)

let diagnostic_to_string (diag : Lang.Diagnostic.t) : string =
  Format.asprintf "%a" pp_diagnostic diag

let print_diagnostics (errors : Lang.Diagnostic.t list) : unit =
  List.iter (fun diag -> print_endline (diagnostic_to_string diag)) errors
