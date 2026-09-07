open Ditto

type t = private (string * string) list

val add_to_env_preserving : string array -> string * string -> string array
val extend_env : string array -> (string * string) list -> string array
val of_array : string array -> (t, Error.t) result
val get : t -> string -> (string, Error.t) result
val get_opt : t -> string -> string option
val int_of_string_err : string -> (int, Error.t) result
val get_as_bool_default : t -> string -> bool -> (bool, Error.t) result
