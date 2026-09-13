let get_line_col_positions (text : string) (pos : int) :
    (Code_point.t, Error.t) result =
  let rec aux line col index =
    if index = pos then (line, col)
    else if index >= String.length text then (line, col)
    else if text.[index] = '\n' then aux (line + 1) 0 (index + 1)
    else aux line (col + 1) (index + 1)
  in

  let line, character = aux 0 0 0 in
  (* Start from line 0, column 0, character 0 *)
  Code_point.make ~line ~character

let mark_string_regions (s : string) : bool array =
  let n = String.length s in
  let rec loop i in_string escape acc =
    if i = n then Array.of_list (List.rev acc)
    else
      let c = s.[i] in

      if in_string then
        let acc' = true :: acc in
        if escape then loop (i + 1) true false acc'
        else begin
          match c with
          | '\\' -> loop (i + 1) true true acc'
          | '"' -> loop (i + 1) false false acc'
          | _ -> loop (i + 1) true false acc'
        end
      else
        (* Outside a string *)
        let acc' = false :: acc in
        match c with
        | '"' -> loop (i + 1) true false acc'
        | _ -> loop (i + 1) false false acc'
  in
  loop 0 false false []

let get_comments (content : string) :
    ((string * Code_point.t) list, Error.t) result =
  let ( let* ) = Result.bind in

  let explode s =
    List.init (String.length s) (fun idx -> (idx, String.get s idx))
  in
  let repr = explode content in

  let pairwise lst =
    let rec aux acc = function
      | (a1, p1) :: (a2, p2) :: rest ->
          aux (((a1, p1), (a2, p2)) :: acc) ((a2, p2) :: rest)
      | _ -> List.rev acc
    in
    aux [] lst
  in

  let string_mask = mark_string_regions content in

  let pairs =
    pairwise repr |> List.filter (fun ((i, _), _) -> not string_mask.(i))
  in
  let* _, res =
    List.fold_left
      (fun acc pair ->
        match acc with
        | Ok (stack, res) as acc -> (
            match pair with
            | ((_, '('), (_, '*')) as x -> Ok (x :: stack, res)
            | (idx1, '*'), (idx2, ')') -> (
                match stack with
                | ((idx3, '('), (idx4, '*')) :: t ->
                    Ok (t, ((idx3, idx4), (idx1, idx2)) :: res)
                | [] ->
                    acc
                    (* we might have encountered: try (rewrite IHn in *\) for example *)
                | _ -> Error.string_to_or_error "unmatched ending comment")
            | _ -> acc)
        | Error err -> Error err)
      (Ok ([], []))
      pairs
  in

  List_utils.map_result
    (fun ((a, _), (_, d)) ->
      let len = d - a + 1 in
      let str = String.sub content a len in
      let start_res = get_line_col_positions content a in
      match start_res with
      | Ok start -> Ok (str, start)
      | Error err -> Error err)
    res
