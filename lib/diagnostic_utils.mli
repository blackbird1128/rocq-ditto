val error_location_to_string : Lang.Range.t -> string
val diagnostic_kind_to_str : Lang.Diagnostic.Severity.t -> string
val pp_diagnostic : Format.formatter -> Lang.Diagnostic.t -> unit
val diagnostic_to_string : Lang.Diagnostic.t -> string
val print_diagnostics : Lang.Diagnostic.t list -> unit
