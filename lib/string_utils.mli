val split_prefix : prefix:string -> string -> (string * string) option
val remove_prefix : string -> prefix:string -> string
val remove_suffix : string -> suffix:string -> string
val contains : substring:string -> string -> bool
val split_at : char -> string -> (string * string, Error.t) result
val cut : string -> string -> (string * string, Error.t) result
val split_words : string -> string list
val split_by_newline : string -> string list
