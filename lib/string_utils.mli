val split_prefix : string -> string -> (string * string) option
val remove_prefix : string -> string -> string
val remove_suffix : string -> string -> string
val contains : substring:string -> string -> bool
val split_at : char -> string -> (string * string, Error.t) result
val split_words : string -> string list
val split_by_newline : string -> string list
