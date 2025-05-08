type counter
(** Type representing a counter *)

val create : unit -> counter
(** Creates a new counter instance *)

val next : counter -> int
(** Returns the next integer in the counter sequence for a given counter *)

val uuid : unit -> Uuidm.t
