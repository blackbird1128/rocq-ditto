val push_range_n_char : int -> Lang.Range.t -> Lang.Range.t
val range_from_starting_point_and_repr : Lang.Point.t -> string -> Lang.Range.t
val are_flat_ranges_colliding : int * int -> int * int -> bool
val common_range : int * int -> int * int -> (int * int) option
