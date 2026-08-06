let split_prefix (prefix : string) (s : string) : (string * string) option =
  let plen = String.length prefix in
  if String.length s >= plen && String.sub s 0 plen = prefix then
    Some (prefix, String.sub s plen (String.length s - plen))
  else None

let remove_prefix (str : string) (prefix : string) =
  let str_len = String.length str in
  let prefix_len = String.length prefix in
  if str_len >= prefix_len && String.starts_with ~prefix str then
    String.sub str prefix_len (str_len - prefix_len)
  else str

let remove_suffix (str : string) (suffix : string) =
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
