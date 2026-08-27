let split_prefix ~(prefix : string) (s : string) : (string * string) option =
  let plen = String.length prefix in
  if String.length s >= plen && String.sub s 0 plen = prefix then
    Some (prefix, String.sub s plen (String.length s - plen))
  else None

let remove_prefix (str : string) ~(prefix : string) =
  let str_len = String.length str in
  let prefix_len = String.length prefix in
  if str_len >= prefix_len && String.starts_with ~prefix str then
    String.sub str prefix_len (str_len - prefix_len)
  else str

let remove_suffix (str : string) ~(suffix : string) =
  let str_len = String.length str in
  let suffix_len = String.length suffix in
  if str_len >= suffix_len && String.ends_with ~suffix str then
    String.sub str 0 (str_len - suffix_len)
  else str

let contains ~(substring : string) (container : string) =
  let sublength = String.length substring in
  let container_length = String.length container in
  let rec loop idx =
    if sublength + idx > container_length then false
    else
      let curr_sub = String.sub container idx sublength in
      if String.equal substring curr_sub then true else loop (idx + 1)
  in
  loop 0

let split_at (split_point : char) (str : string) :
    (string * string, Error.t) result =
  match String.index_opt str split_point with
  | Some idx ->
      let first_part = String.sub str 0 idx in
      let length_second_part = String.length str - (idx + 1) in
      let second_part =
        if length_second_part = 0 then ""
        else String.sub str (idx + 1) length_second_part
      in
      Ok (first_part, second_part)
  | None ->
      Error.format_to_or_error "Couldn't find the split point %C in %S"
        split_point str

let cut (cut_point : string) (container : string) :
    (string * string, Error.t) result =
  let cut_length = String.length cut_point in
  let container_length = String.length container in
  let rec loop idx =
    if cut_length + idx > container_length then
      Error.format_to_or_error "Couldn't find the cut point %S in %S" cut_point
        container
    else
      let cur_sub = String.sub container idx cut_length in
      if String.equal cur_sub cut_point then
        let first_part = String.sub container 0 idx in
        let length_second_part = String.length container - (idx + cut_length) in
        let second_part =
          if length_second_part = 0 then ""
          else String.sub container (idx + cut_length) length_second_part
        in

        Ok (first_part, second_part)
      else loop (idx + 1)
  in
  loop 0

let split_words (line : string) : string list =
  let rec skip_spaces i =
    if i < String.length line then
      match line.[i] with ' ' | '\t' -> skip_spaces (i + 1) | _ -> i
    else i
  in
  let rec take_word i j =
    if j < String.length line then
      match line.[j] with
      | ' ' | '\t' -> (String.sub line i (j - i), j)
      | _ -> take_word i (j + 1)
    else (String.sub line i (j - i), j)
  in
  let rec loop i acc =
    let i = skip_spaces i in
    if i >= String.length line then List.rev acc
    else
      let word, j = take_word i i in
      loop j (word :: acc)
  in
  loop 0 []

let split_by_newline (str : string) : string list =
  let line_by_newlines = String.split_on_char '\n' str in
  let count_line_by_newlines = List.length line_by_newlines in

  line_by_newlines
  |> List.map (fun line ->
      let len = String.length line in
      if count_line_by_newlines > 1 && len > 0 && line.[len - 1] = '\r' then
        String.sub line 0 (len - 1)
      else line)
