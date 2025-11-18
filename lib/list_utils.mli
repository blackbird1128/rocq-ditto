val take : int -> 'a list -> 'a list
val drop : int -> 'a list -> 'a list
val take_while : ('a -> bool) -> 'a list -> 'a list
val drop_while : ('a -> bool) -> 'a list -> 'a list
val last : 'a list -> 'a option
val last_and_len : 'a list -> 'a option * int
val find_index : ('a -> bool) -> 'a list -> int option

val map2_pad :
  ?pad1:'a option ->
  ?pad2:'b option ->
  ('a -> 'b -> 'c) ->
  'a list ->
  'b list ->
  'c list
