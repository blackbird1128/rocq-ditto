module IntHash = struct
  type t = int

  let equal i j = i = j
  let hash i = i land max_int
end

module IntHashtbl = Hashtbl.Make (IntHash)
