type 'a nary_tree = Node of 'a * 'a nary_tree list

let rec equal_nary_tree (equal_a : 'a -> 'a -> bool) (Node (a1, children1))
    (Node (a2, children2)) : bool =
  try
    equal_a a1 a2 && List.for_all2 (equal_nary_tree equal_a) children1 children2
  with Invalid_argument _ -> false

let rec pp_nary_tree (pp_a : Format.formatter -> 'a -> unit)
    (fmt : Format.formatter) (Node (a, children)) : unit =
  (* Print the current node value *)
  Format.fprintf fmt "%a" pp_a a;
  (* If the node has children, print them in parentheses *)
  if children <> [] then (
    Format.fprintf fmt " (";
    List.iteri
      (fun i child ->
        if i > 0 then Format.fprintf fmt ", ";
        (* Add a comma between children *)
        pp_nary_tree pp_a fmt child)
      children;
    Format.fprintf fmt ")")

let rec flatten_filter (f : 'a -> bool) (Node (x, children)) : 'a nary_tree list
    =
  let processed_children = List.concat_map (flatten_filter f) children in
  if f x then
    (* Node matches, keep it and its processed children as one node *)
    [ Node (x, processed_children) ]
  else
    (* Node doesn't match, flatten it by returning its children directly *)
    processed_children

let remove_all_nonmatching (f : 'a -> bool) (tree : 'a nary_tree) :
    'a nary_tree option =
  match flatten_filter f tree with [ result ] -> Some result | _ -> None

let add_child (tree : 'a nary_tree) (child : 'a nary_tree) : 'a nary_tree =
  match tree with Node (x, children) -> Node (x, child :: children)

let rec map (f : 'a -> 'b) (tree : 'a nary_tree) : 'b nary_tree =
  match tree with Node (x, children) -> Node (f x, List.map (map f) children)

let rec depth_first_fold (f : 'acc -> 'a -> 'acc) (acc : 'acc)
    (tree : 'a nary_tree) : 'acc =
  match tree with
  | Node (x, children) ->
      let new_acc = f acc x in
      List.fold_left (depth_first_fold f) new_acc children

let rec flatten (tree : 'a nary_tree) : 'a list =
  match tree with
  | Node (x, children) -> x :: List.concat (List.map flatten children)

let rec flatten_map (f : 'a -> 'b) (tree : 'a nary_tree) : 'b list =
  match tree with
  | Node (x, children) -> f x :: List.concat (List.map (flatten_map f) children)

let rec top_n (n : int) (Node (value, children)) : 'a nary_tree =
  if n <= 0 then Node (value, [])
  else Node (value, List.map (top_n (n - 1)) children)

let rec bottom_n (n : int) (Node (_, children) as tree) =
  if n = 0 then [ tree ]
  else List.flatten (List.map (bottom_n (n - 1)) children)

let rec depth_first_fold_with_state (f : 'acc -> 'a -> 'acc) (acc : 'acc)
    (tree : 'a nary_tree) : 'acc =
  match tree with
  | Node (x, children) ->
      let new_acc = f acc x in
      List.fold_left (depth_first_fold f) new_acc children
