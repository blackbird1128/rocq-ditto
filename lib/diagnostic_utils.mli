open Fleche

val error_location_to_string : Lang.Range.t -> string
val diagnostic_kind_to_str : Lang.Diagnostic.Severity.t -> string
val print_diagnostics : Lang.Diagnostic.t list -> unit
