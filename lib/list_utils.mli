val take : int -> 'a list -> 'a list
val drop : int -> 'a list -> 'a list
val take_while : ('a -> bool) -> 'a list -> 'a list
val drop_while : ('a -> bool) -> 'a list -> 'a list

val map2_pad :
  ?pad1:'a option ->
  ?pad2:'b option ->
  ('a -> 'b -> 'c) ->
  'a list ->
  'b list ->
  'c list
