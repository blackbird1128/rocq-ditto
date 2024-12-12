let counter = ref 0

let next () =
  let id = !counter in
  counter := id + 1;
  id
