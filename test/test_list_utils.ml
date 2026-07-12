open Alcotest
open Ditto.List_utils

let test_head_opt_non_empty () =
  check (option int) "Head opt should get the head when non empty" (Some 0)
    (head_opt [ 0 ])

let test_head_opt_empty () =
  check (option int) "Head opt should get None when there is no head" None
    (head_opt [])

let test_take_less_than_len () =
  check (list int) "take should take the n first item if n <= length"
    [ 1; 2; 3 ]
    (take 3 [ 1; 2; 3; 4 ])

let () =
  run "List utils"
    [
      ( "List utils fun",
        [
          test_case "test head opt get some list head when non empty" `Quick
            test_head_opt_non_empty;
          test_case "test head opt return None when the list is empty" `Quick
            test_head_opt_empty;
          test_case "test taking less than length item from a list" `Quick
            test_take_less_than_len;
        ] );
    ]
