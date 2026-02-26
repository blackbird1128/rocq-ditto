let rec remove_loc (s : Sexplib.Sexp.t) : Sexplib.Sexp.t option =
  match s with
  | Atom _ as a -> Some a
  | List (Atom "loc" :: _) -> None (* drop the whole (loc ...) *)
  | List xs ->
      let xs' = xs |> List.filter_map remove_loc in
      Some (List xs')

let strip_loc (sexp : Sexplib.Sexp.t) : Sexplib.Sexp.t =
  match remove_loc sexp with
  | Some s -> s
  | None -> List [] (* should basically never happen at the top *)
