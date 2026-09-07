open Alcotest
open Ditto.List_utils

let test_head_opt_non_empty () =
  check (option int) "Head opt should get the head when non empty" (Some 0)
    (head_opt [ 0 ])

let test_head_opt_empty () =
  check (option int) "Head opt should get None when there is no head" None
    (head_opt [])

let test_take_empty_prop =
  QCheck.Test.make ~count:1000
    ~name:"taking n elements on an empty list should return an empty list"
    QCheck.(int_pos)
    (fun n -> take n [] = [])

let test_take_zero_prop =
  QCheck.Test.make ~count:1000
    ~name:"taking zero elements should return an empty list"
    QCheck.(list int_small)
    (fun l -> take 0 l = [])

let test_take_less_than_len () =
  check (list int) "take should take the n first item if n <= length"
    [ 1; 2; 3 ]
    (take 3 [ 1; 2; 3; 4 ])

let test_take_exact_len () =
  check (list int) "take should take the n first items if n = length"
    [ 1; 2; 3; 4 ]
    (take 4 [ 1; 2; 3; 4 ])

let test_take_more_than_len () =
  check (list int) "take should take the whole list if n > length"
    [ 1; 2; 3; 4 ]
    (take 5 [ 1; 2; 3; 4 ])

let test_take_raise_negative_args () =
  check_raises "reject negative arguments" (Invalid_argument "List.take")
    (fun () -> ignore (take (-1) []))

let test_drop_empty_prop =
  QCheck.Test.make ~count:1000
    ~name:"dropping n elements on an empty list should return an empty list"
    QCheck.(int_pos)
    (fun n -> drop n [] = [])

let test_drop_zero_prop =
  QCheck.Test.make ~count:1000
    ~name:"dropping zero element should return the initial list"
    QCheck.(list int_small)
    (fun l -> drop 0 l = l)

let test_drop_less_than_len () =
  check (list int) "drop should drop the n first items if n <= length" [ 4 ]
    (drop 3 [ 1; 2; 3; 4 ])

let test_drop_exact_len_prop =
  QCheck.Test.make ~count:1000
    ~name:"drop should drop the whole list if n = length"
    QCheck.(list_size Gen.nat int)
    (fun l -> List.is_empty (drop (List.length l) l))

let test_drop_more_than_len () =
  check (list int) "drop should return an empty list if n > length" []
    (drop 5 [ 1; 2; 3; 4 ])

let test_drop_raise_negative_args () =
  check_raises "reject negative arguments" (Invalid_argument "List.drop")
    (fun () -> ignore (drop (-1) []))

let test_take_while_empty () =
  check (list int) "take while should return an empty list from an empty list"
    []
    (take_while (fun _ -> true) [])

let test_take_while_all_prop =
  QCheck.Test.make ~count:1000
    ~name:"taking while matching every element should return the whole list"
    QCheck.(list int)
    (fun l -> take_while (fun _ -> true) l = l)

let test_take_while_none () =
  check (list int)
    "take while matching no elements should return an empty list " []
    (take_while (fun x -> x > 5) [ 1; 2; 3; 4 ])

let test_take_while_stop_at_first_not_matching () =
  check (list int) "take while stop at the first non matching element"
    [ 1; 2; 3 ]
    (take_while (fun x -> x < 4) [ 1; 2; 3; 4; 1 ])

let test_take_while_single_element_matching () =
  check (list int)
    "take while matching a single element list should return that list" [ 1 ]
    (take_while (fun x -> x = 1) [ 1 ])

let test_take_while_single_element_non_matching () =
  check (list int)
    "take while not matching a single element list should return an empty list"
    []
    (take_while (fun x -> x = 0) [ 1 ])

let test_drop_while_empty () =
  check (list int) "drop while should return an empty list from an empty list"
    []
    (drop_while (fun _ -> true) [])

let test_drop_while_all () =
  check (list int)
    "drop while matching every element should return an empty list" []
    (drop_while (fun _ -> true) [ 1; 2; 3; 4 ])

let test_drop_while_none () =
  check (list int)
    "drop while matching no elements should return the whole list"
    [ 1; 2; 3; 4 ]
    (drop_while (fun x -> x > 5) [ 1; 2; 3; 4 ])

let test_drop_while_stop_at_first_not_matching () =
  check (list int) "drop while stop at the first non matching element" [ 4; 1 ]
    (drop_while (fun x -> x < 4) [ 1; 2; 3; 4; 1 ])

let test_drop_while_single_element_matching () =
  check (list int)
    "drop while matching a single element list should return an empty list" []
    (drop_while (fun x -> x = 1) [ 1 ])

let test_drop_while_single_element_non_matching () =
  check (list int)
    "drop while not matching a single element list should return that list"
    [ 1 ]
    (drop_while (fun x -> x = 0) [ 1 ])

let test_split_while_empty () =
  check
    (pair (list int) (list int))
    "split while should return two empty lists for an empty list" ([], [])
    (split_while (fun _ -> true) [])

let test_split_while_all () =
  check
    (pair (list int) (list int))
    "split while matching every element should return the whole list and an \
     empty list"
    ([ 1; 2; 3; 4 ], [])
    (split_while (fun _ -> true) [ 1; 2; 3; 4 ])

let test_split_while_none () =
  check
    (pair (list int) (list int))
    "split while matching no elements should return an empty list and the \
     whole list"
    ([], [ 1; 2; 3; 4 ])
    (split_while (fun x -> x > 5) [ 1; 2; 3; 4 ])

let test_split_while_stop_at_first_not_matching () =
  check
    (pair (list int) (list int))
    "split while should split at the first non matching element"
    ([ 1; 2; 3 ], [ 4; 1 ])
    (split_while (fun x -> x < 4) [ 1; 2; 3; 4; 1 ])

let test_split_while_single_element_matching () =
  check
    (pair (list int) (list int))
    "split while matching a single element should return it in the first list"
    ([ 1 ], [])
    (split_while (fun x -> x = 1) [ 1 ])

let test_split_while_single_element_non_matching () =
  check
    (pair (list int) (list int))
    "split while not matching a single element should return it in the second \
     list"
    ([], [ 1 ])
    (split_while (fun x -> x = 0) [ 1 ])

let test_split_around_simple () =
  check
    (option (triple (list int) int (list int)))
    "split_around should separate around zero in this case"
    (Some ([ 1; 2; 3 ], 0, [ 4; 5; 6 ]))
    (split_around (fun n -> n = 0) [ 1; 2; 3; 0; 4; 5; 6 ])

let test_split_around_empty () =
  check
    (option (triple (list int) int (list int)))
    "split_around on an empty list should return none" None
    (split_around (fun _ -> true) [])

let test_split_around_single_element_success_prop =
  QCheck.Test.make ~count:1000
    ~name:
      "split_around on a single element list [x] succeeding should return Some \
       ([],x,[])"
    QCheck.(int)
    (fun n ->
      let res = split_around (fun a -> a = n) [ n ] in
      match res with Some ([], x, []) when x = n -> true | _ -> false)

let test_split_around_concat_prop =
  QCheck.Test.make ~count:1000
    ~name:
      "if split_around l is Some (left,a,right) then l = left @ (a :: right)"
    QCheck.(int_range 1 1000)
    (fun n ->
      let l = List.init 1000 (fun n -> n + 1) in
      match split_around (fun x -> x = n) l with
      | Some (left, a, right) -> List.equal Int.equal l (left @ (a :: right))
      | None -> false)

let test_last_empty () =
  check (option int) "Last should return None for an empty list" None (last [])

let test_last_single_element () =
  check (option int) "Last of a single element list is that element" (Some 1)
    (last [ 1 ])

let test_last_regular_list () =
  check (option int) "Last get the last element of a list" (Some 4)
    (last [ 1; 2; 3; 4 ])

let test_split_last_empty () =
  check
    (option (pair (list int) int))
    "Split last should return None for an empty list" None (split_last [])

let test_split_last_single () =
  check
    (option (pair (list int) int))
    "Split last should return ([],x) for a singleton list [x]"
    (Some ([], 1))
    (split_last [ 1 ])

let test_split_last_multiple () =
  check
    (option (pair (list int) int))
    "Split last should correctly separate the last element for a list"
    (Some ([ 1; 2; 3 ], 4))
    (split_last [ 1; 2; 3; 4 ])

let test_split_last_snd_is_last_prop =
  QCheck.Test.make ~count:1000
    ~name:"if split_last is Some _, snd (split_last) l = last l"
    QCheck.(int_range 0 10000)
    (fun n ->
      let l = List.init n (fun x -> x) in
      match split_last l with
      | Some (_, last_elem) -> (
          match last l with
          | Some last_elem_from_last -> last_elem_from_last = last_elem
          | None -> false)
      | None -> true)

let test_split_head_last_simple () =
  let l = [ 0; 1; 2; 3 ] in
  let expected = Some (0, [ 1; 2 ], 3) in
  check
    (option (triple int (list int) int))
    "split_head_last should work on list with more than one element" expected
    (split_head_last l)

let test_split_head_last_empty () =
  check
    (option (triple int (list int) int))
    "split_head_last on an empty list should return None" None
    (split_head_last [])

let test_split_head_last_single_element_prop =
  QCheck.Test.make ~count:1000 ~name:"split_head_last on [x] should return None"
    QCheck.(int)
    (fun x ->
      let l = [ x ] in
      Option.is_empty (split_head_last l))

let test_split_head_last_concat_prop =
  QCheck.Test.make ~count:1000
    ~name:"if split_head_last l = Some (s,m,e) then l = s :: m @ [e]"
    QCheck.(int_range 0 10000)
    (fun n ->
      let l = List.init n (fun x -> x) in
      match split_head_last l with
      | Some (s, m, e) -> List.equal Int.equal l ((s :: m) @ [ e ])
      | None -> List.length l < 2)

let test_last_and_len_empty () =
  check
    (pair (option int) int)
    "last_and_len on an empty list should return None and zero" (None, 0)
    (last_and_len [])

let test_last_and_len_single_element () =
  check
    (pair (option int) int)
    "last_and_len on a single-element list should return that element and one"
    (Some 1, 1) (last_and_len [ 1 ])

let test_last_and_len_regular_list () =
  check
    (pair (option int) int)
    "last_and_len on a regular list should return its final element and length"
    (Some 4, 4)
    (last_and_len [ 1; 2; 3; 4 ])

let test_find_index_empty () =
  check (option int) "find_index on an empty list should return None" None
    (find_index (fun _ -> true) [])

let test_find_index_single_element () =
  check (option int)
    "find_index on a matching single-element list should return zero" (Some 0)
    (find_index (fun x -> x = 1) [ 1 ])

let test_find_index_regular_list () =
  check (option int)
    "find_index should return the index of the first matching element" (Some 2)
    (find_index (fun x -> x = 3) [ 1; 2; 3; 4 ])

let test_find_index_no_match () =
  check (option int) "find_index should return None when there is no match" None
    (find_index (fun x -> x > 4) [ 1; 2; 3; 4 ])

let test_find_last_opt_empty () =
  check (option int) "find_last_opt on an empty list should return None" None
    (find_last_opt (fun _ -> true) [])

let test_find_last_opt_single_element () =
  check (option int)
    "find_last_opt on a matching single-element list should return that element"
    (Some 1)
    (find_last_opt (fun x -> x = 1) [ 1 ])

let test_find_last_opt_regular_list () =
  check (option int) "find_last_opt should return the last matching element"
    (Some 3)
    (find_last_opt (fun x -> x = 3) [ 1; 3; 2; 3; 4 ])

let test_find_last_opt_no_match () =
  check (option int) "find_last_opt should return None when there is no match"
    None
    (find_last_opt (fun x -> x > 4) [ 1; 2; 3; 4 ])

let test_find_last_true_fun_is_last_prop =
  QCheck.Test.make ~count:1000
    ~name:
      "If the fun for find_last return true for all element, it return the \
       last element"
    QCheck.(int_range 1 1000)
    (fun n ->
      let l = List.init n (fun x -> x) in
      match find_last_opt (fun _ -> true) l with
      | Some elem -> (
          match last l with Some last_elem -> elem = last_elem | None -> false)
      | None -> false)

let test_result_all_empty_is_ok () =
  check
    (result (list int) unit)
    "result_all on an empty list should return []" (Ok []) (result_all [])

let test_result_all_simple_with_error () =
  check
    (result (list int) string)
    "result_all on a list with errors should return the first error"
    (Error "err")
    (result_all [ Ok 1; Ok 2; Error "err"; Ok 3 ])

let test_result_all_on_list_of_ok_return_list =
  QCheck.Test.make ~count:1000
    ~name:"result_all on a list l with only (Ok l_i) return l with Ok unwrapped"
    QCheck.(int_range 0 1000)
    (fun n ->
      let l = List.init n (fun x -> x) in
      let l_wrapped = List.map Result.ok l in
      let res = result_all l_wrapped in
      match res with
      | Ok l_res -> List.equal Int.equal l_res l
      | Error _ -> false)

let () =
  let qcheck_tests =
    List.map QCheck_alcotest.to_alcotest
      [
        test_take_zero_prop;
        test_take_empty_prop;
        test_drop_zero_prop;
        test_drop_empty_prop;
        test_drop_exact_len_prop;
        test_take_while_all_prop;
        test_split_around_single_element_success_prop;
        test_split_around_concat_prop;
        test_split_last_snd_is_last_prop;
        test_split_head_last_single_element_prop;
        test_split_head_last_concat_prop;
        test_find_last_true_fun_is_last_prop;
        test_result_all_on_list_of_ok_return_list;
      ]
  in

  run "List utils"
    [
      ("Property tests", qcheck_tests);
      ( "List utils fun",
        [
          test_case "test head opt get some list head when non empty" `Quick
            test_head_opt_non_empty;
          test_case "test head opt return None when the list is empty" `Quick
            test_head_opt_empty;
          test_case "test taking less than length items from a list" `Quick
            test_take_less_than_len;
          test_case "test taking more than length items from a list" `Quick
            test_take_more_than_len;
          test_case "test taking n items from a list of length n" `Quick
            test_take_exact_len;
          test_case "test taking negative items raise invalid_arg" `Quick
            test_take_raise_negative_args;
          test_case "test dropping less than length items from a list" `Quick
            test_drop_less_than_len;
          test_case "test dropping more than length items from a list" `Quick
            test_drop_more_than_len;
          test_case "test dropping negative items raise invalid_arg" `Quick
            test_drop_raise_negative_args;
          test_case "take_while on an empty list should return an empty list"
            `Quick test_take_while_empty;
          test_case
            "take_while matching no elements should return an empty list" `Quick
            test_take_while_none;
          test_case "take_while stop at the first non matching element" `Quick
            test_take_while_stop_at_first_not_matching;
          test_case
            "take_while with a matching predicate on a single element list \
             return that element "
            `Quick test_take_while_single_element_matching;
          test_case
            "take_while with a non matching predicate on a single element list \
             return an empty list"
            `Quick test_take_while_single_element_non_matching;
          test_case "drop_while on an empty list should return an empty list"
            `Quick test_drop_while_empty;
          test_case
            "drop_while matching every element should return an empty list"
            `Quick test_drop_while_all;
          test_case
            "drop_while matching no elements should return the whole list"
            `Quick test_drop_while_none;
          test_case "drop_while stop at the first non matching element" `Quick
            test_drop_while_stop_at_first_not_matching;
          test_case
            "drop_while with a matching predicate on a single element list \
             return an empty list"
            `Quick test_drop_while_single_element_matching;
          test_case
            "drop_while with a non matching predicate on a single element list \
             return that element"
            `Quick test_drop_while_single_element_non_matching;
          test_case "split_while on an empty list should return two empty lists"
            `Quick test_split_while_empty;
          test_case
            "split_while matching every element should return the whole list \
             and an empty list"
            `Quick test_split_while_all;
          test_case
            "split_while matching no elements should return an empty list and \
             the whole list"
            `Quick test_split_while_none;
          test_case "split_while should split at the first non matching element"
            `Quick test_split_while_stop_at_first_not_matching;
          test_case
            "split_while matching a single element should return it in the \
             first list"
            `Quick test_split_while_single_element_matching;
          test_case
            "split_while not matching a single element should return it in the \
             second list"
            `Quick test_split_while_single_element_non_matching;
          test_case "split_around should split a simple list correctly" `Quick
            test_split_around_simple;
          test_case "split_around on an empty list should return None" `Quick
            test_split_around_empty;
          test_case "last on an empty list should return None" `Quick
            test_last_empty;
          test_case "last on a single-element list should return that element"
            `Quick test_last_single_element;
          test_case "last on a regular list should return its final element"
            `Quick test_last_regular_list;
          test_case "last_and_len on an empty list should return None and zero"
            `Quick test_last_and_len_empty;
          test_case
            "last_and_len on a single-element list should return that element \
             and one"
            `Quick test_last_and_len_single_element;
          test_case
            "last_and_len on a regular list should return its final element \
             and length"
            `Quick test_last_and_len_regular_list;
          test_case "split last on an empty list should return None" `Quick
            test_split_last_empty;
          test_case
            "split last on a singleton list [x] should return Some([],x)" `Quick
            test_split_last_single;
          test_case
            "split last on a non empty list should correctly split that list"
            `Quick test_split_last_multiple;
          test_case
            "split head last on a list with length > 1 correctly split that \
             list"
            `Quick test_split_head_last_simple;
          test_case "split head last on an empty list should return None" `Quick
            test_split_head_last_empty;
          test_case "find_index on an empty list should return None" `Quick
            test_find_index_empty;
          test_case
            "find_index on a matching single-element list should return zero"
            `Quick test_find_index_single_element;
          test_case
            "find_index should return the index of the first matching element"
            `Quick test_find_index_regular_list;
          test_case "find_index should return None when there is no match"
            `Quick test_find_index_no_match;
          test_case "find_last_opt on an empty list should return None" `Quick
            test_find_last_opt_empty;
          test_case
            "find_last_opt on a matching single-element list should return \
             that element"
            `Quick test_find_last_opt_single_element;
          test_case "find_last_opt should return the last matching element"
            `Quick test_find_last_opt_regular_list;
          test_case "find_last_opt should return None when there is no match"
            `Quick test_find_last_opt_no_match;
          test_case "result_all on [] should return Ok []" `Quick
            test_result_all_empty_is_ok;
          test_case
            "result_all on a list with errors should return the first error "
            `Quick test_result_all_simple_with_error;
        ] );
    ]
