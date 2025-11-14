[%%import "rocq_version_optcomp.mlh"]
[%%if rocq_version < (9, 1, 0)]

type goal_range_selector =
  | NthSelector of int
  | RangeSelector of int * int
  | IdSelector of Names.Id.t

type t =
  | SelectAlreadyFocused
  | SelectList of goal_range_selector list
  | SelectAll

let make (x : Goal_select.t) : t =
  match x with
  | Goal_select.SelectAlreadyFocused -> SelectAlreadyFocused
  | Goal_select.SelectNth nth -> SelectList [ NthSelector nth ]
  | Goal_select.SelectList range_list ->
      let l = List.map (fun (a, b) -> RangeSelector (a, b)) range_list in
      SelectList l
  | Goal_select.SelectId id -> SelectList [ IdSelector id ]
  | Goal_select.SelectAll -> SelectAll

let to_goal_select (x : t) : Goal_select.t =
  match x with
  | SelectAlreadyFocused -> Goal_select.SelectAlreadyFocused
  | SelectAll -> Goal_select.SelectAll
  | SelectList selectors -> (
      match selectors with
      | [ NthSelector n ] -> Goal_select.SelectNth n
      | [ RangeSelector (a, b) ] -> Goal_select.SelectList [ (a, b) ]
      | [ IdSelector id ] -> Goal_select.SelectId id
      | lst ->
          let ranges =
            List.filter_map
              (function
                | RangeSelector (a, b) -> Some (a, b)
                | NthSelector n -> Some (n, n)
                | IdSelector _ -> None)
              lst
          in
          Goal_select.SelectList ranges)

[%%else]

type goal_range_selector = [%import: Proofview.goal_range_selector]
[@@derive show]

type t = [%import: Goal_select.t]

let make (x : Goal_select.t) : t = x
let to_goal_select (x : t) = x

[%%endif]

let pp_goal_range_selector (fmt : Format.formatter) (x : goal_range_selector) =
  match x with
  | NthSelector nth -> Format.fprintf fmt "NthSelector %d" nth
  | RangeSelector (start, end_) ->
      Format.fprintf fmt "RangeSelector (%d,%d)" start end_
  | IdSelector name ->
      let name_str = Names.Id.to_string name in
      Format.fprintf fmt "IdSelector (%s)" name_str

let goal_range_selector_to_string (x : goal_range_selector) : string =
  Format.asprintf "%a" pp_goal_range_selector x

let pp (fmt : Format.formatter) (x : t) =
  match x with
  | SelectAlreadyFocused -> Format.fprintf fmt "SelectAlreadyFocused"
  | SelectList select_list ->
      Format.fprintf fmt "SelectList (%a)"
        (Format.pp_print_list ?pp_sep:(Some Format.pp_print_space)
           pp_goal_range_selector)
        select_list
  | SelectAll -> Format.fprintf fmt "SelectAll"

let to_string (x : t) : string = Format.asprintf "%a" pp x

let range_to_list i j =
  let rec aux n acc = if n < i then acc else aux (n - 1) (n :: acc) in
  aux j []

let apply_goal_selector_view (x : t) (goals : 'a Coq.Goals.Reified_goal.t list)
    : ('a Coq.Goals.Reified_goal.t list, Error.t) result =
  match x with
  | SelectAlreadyFocused ->
      if List.length goals = 1 then Ok goals
      else Error.string_to_or_error "Can't select with (!:) more than one goals"
  | SelectList select_list ->
      let selected =
        List.fold_left
          (fun (acc : 'a Coq.Goals.Reified_goal.t option list)
               (x : goal_range_selector) ->
            match x with
            | NthSelector n -> List.nth_opt goals (n - 1) :: acc
            | RangeSelector (start, end_) ->
                let range_list = range_to_list start end_ in
                List.map (fun n -> List.nth_opt goals (n - 1)) range_list @ acc
            | IdSelector id ->
                let goal =
                  List.find
                    (fun (x : 'a Coq.Goals.Reified_goal.t) ->
                      Option.equal ( = ) x.info.name (Some id))
                    goals
                in
                [ Some goal ])
          [] select_list
      in
      if List.for_all Option.has_some selected then
        Ok (List.map Option.get selected)
      else
        Error.string_to_or_error
          "Failed to get one or more of the goal in the goal selector"
  | SelectAll -> Ok goals
