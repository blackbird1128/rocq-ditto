type 'a nary_tree = Node of 'a * 'a nary_tree list

let rec equal_nary_tree equal_a (Node (a1, children1)) (Node (a2, children2)) =
  try
    equal_a a1 a2 && List.for_all2 (equal_nary_tree equal_a) children1 children2
  with Invalid_argument _ -> false

let rec pp_nary_tree pp_a fmt (Node (a, childrens)) =
  (* Print the current node value *)
  Format.fprintf fmt "%a" pp_a a;
  (* If the node has children, print them in parentheses *)
  if childrens <> [] then (
    Format.fprintf fmt " (";
    List.iteri
      (fun i child ->
        if i > 0 then Format.fprintf fmt ", ";
        (* Add a comma between children *)
        pp_nary_tree pp_a fmt child)
      childrens;
    Format.fprintf fmt ")")

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

let rec map (f : 'a -> 'b) (tree : 'a nary_tree) : 'b nary_tree =
  match tree with Node (x, childrens) -> Node (f x, List.map (map f) childrens)

let rec depth_first_fold (f : 'acc -> 'a -> 'acc) (acc : 'acc)
    (tree : 'a nary_tree) : 'acc =
  match tree with
  | Node (x, childrens) ->
      let new_acc = f acc x in
      List.fold_left (depth_first_fold f) new_acc childrens

let rec flatten (tree : 'a nary_tree) : 'a list =
  match tree with
  | Node (x, childrens) -> x :: List.concat (List.map flatten childrens)

let rec flatten_map (f : 'a -> 'b) (tree : 'a nary_tree) : 'b list =
  match tree with
  | Node (x, childrens) ->
      f x :: List.concat (List.map (flatten_map f) childrens)
