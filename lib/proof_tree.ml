type 'a nary_tree = Node of 'a * 'a nary_tree list

let rec equal_nary_tree equal_a (Node (a1, children1)) (Node (a2, children2)) =
  equal_a a1 a2 && List.for_all2 (equal_nary_tree equal_a) children1 children2

let rec pp_nary_tree pp_a fmt (Node (a, children)) =
  Format.fprintf fmt "Node (%a, [%a])"
    pp_a a
    (Format.pp_print_list (pp_nary_tree pp_a)) children

let rec flatten_filter f (Node (x, children)) : 'a nary_tree list =
  let processed_children = List.concat_map (flatten_filter f) children in
  if f x then
    (* Node matches, keep it and its processed children as one node *)
    [ Node (x, processed_children) ]
  else
    (* Node doesn't match, flatten it by returning its children directly *)
    processed_children

let remove_all_nonmatching f tree =
  match flatten_filter f tree with [ result ] -> Some result | _ -> None
