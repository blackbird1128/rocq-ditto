let to_result (opt : 'a option) ~(none : ('a, 'b) result) : ('a, 'b) result =
  match opt with Some v -> Ok v | None -> none
