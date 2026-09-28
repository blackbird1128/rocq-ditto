open Ditto

type t

val empty : t
val pp : Format.formatter -> t -> unit
val to_string : t -> string
val of_step_list : Transforming_step.t list -> t
val add : t -> t -> t
