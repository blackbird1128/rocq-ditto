open Ditto

type t = (string * string) list

let equal (a : t) (b : t) =
  List.equal
    (fun (key_a, value_a) (key_b, value_b) ->
      String.equal key_a key_b && String.equal value_a value_b)
    a b

let pp_key_value (fmt : Format.formatter) (key_value : string * string) =
  let key, value = key_value in
  Format.pp_print_string fmt (Format.sprintf "(%s = %s)" key value)

let pp (fmt : Format.formatter) (env : t) =
  Format.fprintf fmt "[@[%a@]]"
    (Format.pp_print_list
       ~pp_sep:(fun fmt () -> Format.fprintf fmt ";@ ")
       pp_key_value)
    env

let empty = []
let of_assoc_list (a_list : (string * string) list) : t = a_list
let to_assoc_list (a : t) : (string * string) list = a

(* Already set values take precedence *)
(* TODO: check if this is the better solution *)
let add_to_env_preserving (env : string array) (assoc : string * string) :
    string array =
  let key, value = assoc in
  let env_list = Array.to_list env in
  let assoc_key_repr = Printf.sprintf "%s=" key in
  let assoc_repr = assoc_key_repr ^ value in
  match
    List.find_opt
      (fun env_val -> String.starts_with ~prefix:assoc_key_repr env_val)
      env_list
  with
  | Some _ -> env
  | None -> Array.of_list (assoc_repr :: env_list)

(* Already set values take precedence *)
(* TODO: check if this is the better solution *)
let extend_env (env_array : string array) (values : (string * string) list) :
    string array =
  List.fold_left
    (fun env_acc assoc -> add_to_env_preserving env_acc assoc)
    env_array values

let of_array (env_array : string array) : (t, Error.t) result =
  let env_list = Array.to_list env_array in
  let rec aux (acc : t) = function
    | [] -> Ok (List.rev acc)
    | x :: tail -> (
        let split = String_utils.split_at '=' x in
        match split with
        | Ok (key, value) -> aux ((key, value) :: acc) tail
        | Error _ ->
            Error.format_to_or_error
              "Malformed environment: Got %S instead of a value of the shape \
               \"key=value\""
              x)
  in
  aux [] env_list

let to_array (env : t) : string array =
  List.map (fun (key, value) -> Format.sprintf "%S=%S" key value) env
  |> Array.of_list

let get (env : t) (key : string) : (string, Error.t) result =
  match List.assoc_opt key env with
  | Some key -> Ok key
  | None -> Error.format_to_or_error "key: %S not found in environment" key

let get_opt (env : t) (key : string) : string option = List.assoc_opt key env

let int_of_string_err (arg : string) : (int, Error.t) result =
  match int_of_string_opt arg with
  | Some integer -> Ok integer
  | None ->
      Error.format_to_or_error
        "given string %S is not a valid representation of an integer" arg

let get_as_bool_default (env : t) (key : string) (default : bool) :
    (bool, Error.t) result =
  match List.assoc_opt key env with
  | Some env_val -> (
      match env_val with
      | "true" -> Ok true
      | "false" -> Ok false
      | _ ->
          Error.format_to_or_error
            "value %S of key %S can't be converted to a boolean" env_val key)
  | None -> Ok default
