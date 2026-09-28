let line_starts (text : string) : int array =
  let length = String.length text in
  let rec scan index starts =
    if index = length then Array.of_list (List.rev starts)
    else if text.[index] = '\n' then scan (index + 1) ((index + 1) :: starts)
    else scan (index + 1) starts
  in
  scan 0 [ 0 ]

let get_line_col_positions (starts : int array) (pos : int) :
    (Code_point.t, Error.t) result =
  let rec find_line low high =
    if low = high then low
    else
      let mid = (low + high + 1) / 2 in
      if starts.(mid) <= pos then find_line mid high
      else find_line low (mid - 1)
  in
  let line = find_line 0 (Array.length starts - 1) in
  Code_point.make ~line ~character:(pos - starts.(line))

let mark_string_regions (s : string) : bool array =
  let n = String.length s in
  let marks = Array.make n false in
  let rec loop i in_string escape =
    if i < n then (
      let c = s.[i] in
      marks.(i) <- in_string;
      if in_string then
        if escape then loop (i + 1) true false
        else
          match c with
          | '\\' -> loop (i + 1) true true
          | '"' -> loop (i + 1) false false
          | _ -> loop (i + 1) true false
      else
        match c with
        | '"' -> loop (i + 1) true false
        | _ -> loop (i + 1) false false)
  in
  loop 0 false false;
  marks

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
                    if idx1 <= idx4 then acc
                    else Ok (t, ((idx3, idx4), (idx1, idx2)) :: res)
                | [] ->
                    acc
                    (* we might have encountered: try (rewrite IHn in *\) for example *)
                | _ -> Error.string_to_or_error "unmatched ending comment")
            | _ -> acc)
        | Error err -> Error err)
      (Ok ([], []))
      pairs
  in

  match res with
  | [] -> Ok []
  | _ ->
      let starts = line_starts content in
      List_utils.map_result
        (fun ((a, _), (_, d)) ->
          let len = d - a + 1 in
          let str = String.sub content a len in
          let start_res = get_line_col_positions starts a in
          match start_res with
          | Ok start -> Ok (str, start)
          | Error err -> Error err)
        res
