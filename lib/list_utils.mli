val head_opt : 'a list -> 'a option
val take : int -> 'a list -> 'a list
val drop : int -> 'a list -> 'a list
val take_while : ('a -> bool) -> 'a list -> 'a list
val drop_while : ('a -> bool) -> 'a list -> 'a list
val last : 'a list -> 'a option
val last_and_len : 'a list -> 'a option * int
val find_index : ('a -> bool) -> 'a list -> int option
val find_last_opt : ('a -> bool) -> 'a list -> 'a option
val dedup : 'a list -> 'a list
val option_all : 'a option list -> 'a list option
val result_all : ('a, 'e) result list -> ('a list, 'e) result
val concat_result : ('a list, 'e) result list -> ('a list, 'e) result

val concat_map_result :
  ('a -> ('b list, 'e) result) -> 'a list -> ('b list, 'e) result

val map2_pad :
  ?pad1:'a option ->
  ?pad2:'b option ->
  ('a -> 'b -> 'c) ->
  'a list ->
  'b list ->
  'c list
