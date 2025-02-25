type counter = { count : int ref }

let create () = { count = ref 0 }

let next c =
  let id = !(c.count) in
  c.count := id + 1;
  id
