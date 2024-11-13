module RequestCounter = struct
  let counter = ref 0

  let next () =
    let current = !counter in
    counter := !counter + 1;
    current
end
