let to_result (opt : 'a option) ~(none : ('a, 'b) result) : ('a, 'b) result =
  match opt with Some v -> Ok v | None -> none

let to_list (opt : 'a option) : 'a list =
  match opt with Some x -> [ x ] | None -> []

let pair (a : 'a option) (b : 'b option) : ('a * 'b) option =
  match (a, b) with Some a, Some b -> Some (a, b) | _ -> None
