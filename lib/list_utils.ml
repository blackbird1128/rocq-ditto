let take (n : int) (l : 'a list) =
  let[@tail_mod_cons] rec aux (n : int) (l : 'a list) =
    match (n, l) with 0, _ | _, [] -> [] | n, x :: l -> x :: aux (n - 1) l
  in
  if n < 0 then invalid_arg "List.take";
  aux n l

let drop (n : int) (l : 'a list) =
  let rec aux (i : int) = function
    | _x :: l when i < n -> aux (i + 1) l
    | rest -> rest
  in
  if n < 0 then invalid_arg "List.drop";
  aux 0 l

let take_while (p : 'a -> bool) (l : 'a list) =
  let[@tail_mod_cons] rec aux = function
    | x :: l when p x -> x :: aux l
    | _rest -> []
  in
  aux l

let rec drop_while (p : 'a -> bool) = function
  | x :: l when p x -> drop_while p l
  | rest -> rest

let rec last (l : 'a list) : 'a option =
  match l with
  | [] -> None
  | [ x ] -> Some x
  | _ :: tail -> (last [@tailcall]) tail

let last_and_len (lst : 'a list) : 'a option * int =
  let rec aux (last : 'a option) (count : int) = function
    | [] -> (last, count)
    | x :: xs -> (aux [@tailcall]) (Some x) (count + 1) xs
  in
  aux None 0 lst

let find_index (f : 'a -> bool) (xs : 'a list) =
  let rec aux i = function
    | [] -> None
    | x :: rest -> if f x then Some i else aux (i + 1) rest
  in
  aux 0 xs

let find_last_opt (p : 'a -> bool) (l : 'a list) : 'a option =
  List.fold_left (fun acc x -> if p x then Some x else acc) None l

let option_all (xs : 'a option list) : 'a list option =
  let rec go acc = function
    | [] -> Some (List.rev acc)
    | None :: _ -> None
    | Some x :: tl -> go (x :: acc) tl
  in
  go [] xs

let result_all (xs : ('a, 'e) result list) : ('a list, 'e) result =
  List.fold_left
    (fun acc x ->
      match (acc, x) with
      | Error e, _ -> Error e
      | Ok _, Error e -> Error e
      | Ok ys, Ok y -> Ok (y :: ys))
    (Ok []) xs
  |> Result.map List.rev

let concat_result (l : ('a list, 'e) result list) : ('a list, 'e) result =
  let rec aux acc = function
    | [] -> Ok (List.rev acc)
    | Error e :: _ -> Error e
    | Ok xs :: tl -> aux (List.rev_append xs acc) tl
  in
  aux [] l

let concat_map_result (f : 'a -> ('b list, 'e) result) (l : 'a list) :
    ('b list, 'e) result =
  let rec aux acc = function
    | [] -> Ok (List.rev acc)
    | x :: xs -> (
        match f x with
        | Error e -> Error e
        | Ok ys ->
            (* prepend ys (in order) onto acc *)
            aux (List.rev_append ys acc) xs)
  in
  aux [] l

let map2_pad ?(pad1 = None) ?(pad2 = None) (f : 'a -> 'b -> 'c) (l1 : 'a list)
    (l2 : 'b list) : 'c list =
  let rec aux (acc : 'c list) (l1 : 'a list) (l2 : 'b list) =
    match (l1, l2) with
    | x1 :: t1, x2 :: t2 -> aux (f x1 x2 :: acc) t1 t2
    | [], x2 :: t2 -> (
        match pad1 with
        | Some d1 -> aux (f d1 x2 :: acc) [] t2
        | None -> aux acc [] t2)
    | x1 :: t1, [] -> (
        match pad2 with
        | Some d2 -> aux (f x1 d2 :: acc) t1 []
        | None -> aux acc t1 [])
    | [], [] -> List.rev acc
  in
  aux [] l1 l2
