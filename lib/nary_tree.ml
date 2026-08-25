type 'a t = Node of 'a * 'a t list

let rec equal (equal_a : 'a -> 'a -> bool) (Node (a1, children1))
    (Node (a2, children2)) : bool =
  equal_a a1 a2 && List.equal (equal equal_a) children1 children2

let rec sexp_of (sexp_of_a : 'a -> Sexplib.Sexp.t) (Node (v, children)) :
    Sexplib.Sexp.t =
  List [ sexp_of_a v; List (List.map (sexp_of sexp_of_a) children) ]

let pp_sep fmt () = Format.fprintf fmt ",@ "

let rec pp (pp_a : Format.formatter -> 'a -> unit) (fmt : Format.formatter)
    (Node (a, children)) : unit =
  Format.fprintf fmt "%a" pp_a a;

  if children <> [] then (
    Format.fprintf fmt " (";
    Format.pp_print_list ~pp_sep (pp pp_a) fmt children;
    Format.fprintf fmt ")")

let rec from_parents (cur_node : 'a) (parents : ('a, 'a) Hashtbl.t) : 'a t =
  let childs = Hashtbl.find_all parents cur_node in
  Node (cur_node, List.rev_map (fun node -> from_parents node parents) childs)

let rec flatten_filter (f : 'a -> bool) (Node (x, children)) : 'a t list =
  let processed_children = List.concat_map (flatten_filter f) children in
  if f x then
    (* Node matches, keep it and its processed children as one node *)
    [ Node (x, processed_children) ]
  else
    (* Node doesn't match, flatten it by returning its children directly *)
    processed_children

let filter (f : 'a -> bool) (tree : 'a t) : 'a t option =
  match flatten_filter f tree with [ result ] -> Some result | _ -> None

let add_child (tree : 'a t) (child : 'a t) : 'a t =
  match tree with Node (x, children) -> Node (x, child :: children)

let rec iter (f : 'a -> unit) (tree : 'a t) : unit =
  match tree with
  | Node (x, children) ->
      f x;
      List.iter (iter f) children

let rec map (f : 'a -> 'b) (tree : 'a t) : 'b t =
  match tree with Node (x, children) -> Node (f x, List.map (map f) children)

let rec depth_first_fold (f : 'acc -> 'a -> 'acc) (acc : 'acc) (tree : 'a t) :
    'acc =
  match tree with
  | Node (x, children) ->
      let new_acc = f acc x in
      List.fold_left (depth_first_fold f) new_acc children

let rec depth_first_fold_with_children (f : 'acc -> 'a -> 'a list -> 'acc)
    (acc : 'acc) (tree : 'a t) : 'acc =
  match tree with
  | Node (x, children) ->
      let children_nodes =
        List.map (fun t -> match t with Node (x, _) -> x) children
      in
      let new_acc = f acc x children_nodes in
      List.fold_left (depth_first_fold_with_children f) new_acc children

let rec depth_first_fold_with_children_as_trees
    (f : 'acc -> 'a -> 'a t list -> 'acc) (acc : 'acc) (tree : 'a t) : 'acc =
  match tree with
  | Node (x, children) ->
      let new_acc = f acc x children in
      List.fold_left
        (depth_first_fold_with_children_as_trees f)
        new_acc children

let rec depth_first_fold_map (f : 'acc -> 'a -> 'acc * 'b) (acc : 'acc)
    (tree : 'a t) : 'acc * 'b t =
  match tree with
  | Node (x, children) ->
      let new_acc, new_x = f acc x in
      let final_acc, new_children =
        List.fold_left
          (fun (cur_acc, mapped_children) child ->
            let updated_acc, new_child = depth_first_fold_map f cur_acc child in
            (updated_acc, new_child :: mapped_children))
          (new_acc, []) (List.rev children)
      in
      (final_acc, Node (new_x, List.rev new_children))

let mapi (f : int -> 'a -> 'b) (tree : 'a t) : 'b t =
  snd (depth_first_fold_map (fun i x -> (i + 1, f i x)) 0 tree)

let rec flatten (tree : 'a t) : 'a list =
  match tree with Node (x, children) -> x :: List.concat_map flatten children

let rec flatten_map (f : 'a -> 'b) (tree : 'a t) : 'b list =
  match tree with
  | Node (x, children) -> f x :: List.concat_map (flatten_map f) children

let rec top_n (n : int) (Node (value, children)) : 'a t =
  if n <= 0 then Node (value, [])
  else Node (value, List.map (top_n (n - 1)) children)

let rec bottom_n (n : int) (Node (_, children) as tree) : 'a t list =
  if n = 0 then [ tree ]
  else List.flatten (List.map (bottom_n (n - 1)) children)

let root (tree : 'a t) : 'a = match tree with Node (x, _) -> x
