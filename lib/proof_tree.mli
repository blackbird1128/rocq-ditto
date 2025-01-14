type 'a nary_tree = Node of 'a * 'a nary_tree list

val remove_all_nonmatching : ('a -> bool) -> 'a nary_tree -> 'a nary_tree option

val equal_nary_tree : ('a -> 'a -> bool) -> 'a nary_tree -> 'a nary_tree -> bool
(** Compare two n-ary trees for equality. [equal_nary_tree equal_a tree1 tree2]
    returns [true] if [tree1] and [tree2] are structurally equal and their
    elements satisfy [equal_a]. *)

val pp_nary_tree :
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a nary_tree -> unit
(** [pp_nary_tree pp_a fmt (Node (a, children))] prints the n-ary tree with root
    value [a] and [children] using the printer [pp_a] *)

val add_child : 'a nary_tree -> 'a nary_tree -> 'a nary_tree
val depth_first_fold : ('acc -> 'a -> 'acc) -> 'acc -> 'a nary_tree -> 'acc
val map : ('a -> 'b) -> 'a nary_tree -> 'b nary_tree
val flatten : 'a nary_tree -> 'a list
val flatten_map : ('a -> 'b) -> 'a nary_tree -> 'b list
val top_n : int -> 'a nary_tree -> 'a nary_tree
val bottom_n : int -> 'a nary_tree -> 'a nary_tree list
