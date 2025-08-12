val push_range_n_char : int -> Lang.Range.t -> Lang.Range.t
val range_from_starting_point_and_repr : Code_point.t -> string -> Code_range.t
val are_flat_ranges_colliding : int * int -> int * int -> bool
val common_range : int * int -> int * int -> (int * int) option
