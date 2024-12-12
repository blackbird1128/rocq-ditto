type 'a nary_tree = Node of 'a * 'a nary_tree list

val remove_all_nonmatching : ('a -> bool) -> 'a nary_tree -> 'a nary_tree option
