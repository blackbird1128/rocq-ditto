open Ditto
open Ditto.Transforming_step

type t = {
  add_count : int;
  remove_count : int;
  replace_count : int;
  attach_count : int;
}

let empty =
  { add_count = 0; remove_count = 0; replace_count = 0; attach_count = 0 }

let pp (fmt : Format.formatter) (r : t) : unit =
  Format.fprintf fmt "{Add: %d; Remove: %d; Replace: %d; Attach: %d}"
    r.add_count r.remove_count r.replace_count r.attach_count

let to_string (x : t) : string = Format.asprintf "%a" pp x

let of_step_list (step_list : Transforming_step.t list) : t =
  let rec count (s_acc : t) = function
    | [] -> s_acc
    | step :: tail -> (
        match step with
        | Add _ -> count { s_acc with add_count = s_acc.add_count + 1 } tail
        | Remove _ ->
            count { s_acc with remove_count = s_acc.remove_count + 1 } tail
        | Replace _ ->
            count { s_acc with replace_count = s_acc.replace_count + 1 } tail
        | Attach _ ->
            count { s_acc with attach_count = s_acc.attach_count + 1 } tail)
  in
  count empty step_list

let add (a : t) (b : t) : t =
  {
    add_count = a.add_count + b.add_count;
    remove_count = a.remove_count + b.remove_count;
    replace_count = a.replace_count + b.replace_count;
    attach_count = a.attach_count + b.attach_count;
  }
