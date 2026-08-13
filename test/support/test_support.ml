open Ditto
open Ditto.Nary_tree

let sorted_string_testable =
  Alcotest.testable
    Fmt.Dump.(list string)
    (fun a b -> List.sort String.compare a = List.sort String.compare b)

let testable_nary_tree (pp_a : Format.formatter -> 'a -> unit)
    (equal_a : 'a -> 'a -> bool) : 'a nary_tree Alcotest.testable =
  Alcotest.testable (pp_nary_tree pp_a) (equal_nary_tree equal_a)

let proof_status_testable = Alcotest.testable Proof.pp_proof_status ( = )
let range_testable = Alcotest.testable Code_range.pp ( = )
let uuidm_testable = Alcotest.testable Uuidm.pp ( = )
let error_testable = Alcotest.testable Error.pp ( = )
let goal_select_view_testable = Alcotest.testable Goal_select_view.pp ( = )
let sexp_testable = Alcotest.testable Sexplib.Sexp.pp_hum Sexplib.Sexp.equal
let reified_goal_testable = Alcotest.testable Reified_goal.pp ( = )

let vernacexpr_testable =
  Alcotest.testable
    (fun (fmt : Format.formatter) (x : Vernacexpr.vernac_expr) ->
      let repr = Ppvernac.pr_vernac_expr x in
      Pp.pp_with fmt repr)
    ( = )

let vernac_control_gen_r_testable =
  Alcotest.testable
    (fun (fmt : Format.formatter)
         (x :
           ( Vernacexpr.control_flag,
             Vernacexpr.synterp_vernac_expr )
           Vernacexpr.vernac_control_gen_r) ->
      let x_wrapped = CAst.make x in
      let x = Ppvernac.pr_vernac x_wrapped in
      Pp.pp_with fmt x)
    ( = )

let synterp_vernac_expr_testable =
  Alcotest.testable
    (fun (fmt : Format.formatter) (x : Vernacexpr.synterp_vernac_expr) ->
      let s = Serlib.Ser_vernacexpr.sexp_of_synterp_vernac_expr x in
      Sexplib.Sexp.pp_mach fmt s)
    ( = )

let expect_ok ~(context : string) ~(pp_error : 'e Fmt.t) : ('a, 'e) result -> 'a
    = function
  | Ok value -> value
  | Error err ->
      Alcotest.failf "%s: expected Ok, got Error: %a" context pp_error err

let expect_some ~(context : string) : 'a option -> 'a = function
  | Some value -> value
  | None -> Alcotest.failf "%s: expected Some, got None" context

let expect_single ~(context : string) ~(pp : 'a Fmt.t) : 'a list -> 'a =
  function
  | [ value ] -> value
  | values ->
      Alcotest.failf "%s: expected exactly one element, got %d: %a" context
        (List.length values)
        Fmt.(Dump.list pp)
        values

let expect_nth ~(context : string) ~(pp : 'a Fmt.t) (index : int)
    (values : 'a list) : 'a =
  match List.nth_opt values index with
  | Some value -> value
  | None ->
      Alcotest.failf
        "%s: expected an element at index %d, but list length is %d: %a" context
        index (List.length values)
        Fmt.(Dump.list pp)
        values

let expect_result_ok ?(context = "Expected Ok") (result : ('a, Error.t) result)
    =
  expect_ok ~context ~pp_error:Error.pp result

let expect_head ~(context : string) (values : 'a list) : 'a =
  match values with
  | value :: _ -> value
  | [] -> Alcotest.failf "%s: expected a non-empty list" context

let expect_nth_default (index : int) (values : 'a list) : 'a =
  expect_nth ~context:"Expected an element at the requested index"
    ~pp:(fun fmt _ -> Format.pp_print_string fmt "<value>")
    index values

let expect_error ~(context : string) : ('a, 'e) result -> 'e = function
  | Error err -> err
  | Ok _ -> Alcotest.failf "%s: expected Error, got Ok" context

let check_list_unique ~(eq : 'a -> 'a -> bool) ~(pp : 'a Fmt.t) (lst : 'a list)
    : unit =
  let rec find_duplicate idx = function
    | [] -> None
    | x :: rest -> (
        let rec find_in_rest duplicate_idx = function
          | [] -> None
          | y :: ys ->
              if eq x y then Some (idx, duplicate_idx, x)
              else find_in_rest (duplicate_idx + 1) ys
        in
        match find_in_rest (idx + 1) rest with
        | Some _ as duplicate -> duplicate
        | None -> find_duplicate (idx + 1) rest)
  in
  match find_duplicate 0 lst with
  | None -> ()
  | Some (first_idx, duplicate_idx, value) ->
      let pp_list = Fmt.Dump.list pp in
      let list_str = Format.asprintf "@[<v>Full list:@ %a@]" pp_list lst in
      Alcotest.failf
        "List contains duplicate elements at indices %d and %d: %a\n%s"
        first_idx duplicate_idx pp value list_str

let check_list_sorted ~(cmp : 'a -> 'a -> int) ~(pp : 'a Fmt.t) (lst : 'a list)
    : unit =
  let rec find_failure idx = function
    | [] | [ _ ] -> None
    | x :: y :: rest ->
        if cmp x y <= 0 then find_failure (idx + 1) (y :: rest)
        else Some (idx, x, y)
  in
  match find_failure 0 lst with
  | None -> ()
  | Some (idx, x, y) ->
      let pp_list = Fmt.Dump.list pp in
      let list_str = Format.asprintf "@[<v>Full list:@ %a@]" pp_list lst in
      Alcotest.failf "List is not sorted at index %d: %a > %a\n%s" idx pp x pp y
        list_str
