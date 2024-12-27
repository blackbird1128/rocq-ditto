type 'a nary_tree = Node of 'a * 'a nary_tree list

val remove_all_nonmatching : ('a -> bool) -> 'a nary_tree -> 'a nary_tree option

val equal_nary_tree : ('a -> 'a -> bool) -> 'a nary_tree -> 'a nary_tree -> bool
(** Compare two n-ary trees for equality.
  [equal_nary_tree equal_a tree1 tree2] returns [true] if [tree1] and [tree2]
  are structurally equal and their elements satisfy [equal_a].
*)

val pp_nary_tree :
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a nary_tree -> unit
(** Pretty-printer for n-ary trees. 
  [pp_nary_tree pp_a fmt tree] prints the [tree] to the formatter [fmt]
  using [pp_a] to print elements of type ['a].
 *)

val flatten : 'a nary_tree -> 'a list
val flatten_map : ('a -> 'b) -> 'a nary_tree -> 'b list
