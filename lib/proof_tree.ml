type 'a nary_tree = Node of 'a * 'a nary_tree list

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
