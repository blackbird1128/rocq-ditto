open Ditto.Nary_tree
open Ditto

val sorted_string_testable : string list Alcotest.testable
val proof_status_testable : Proof.proof_status Alcotest.testable
val range_testable : Code_range.t Alcotest.testable
val uuidm_testable : Uuidm.t Alcotest.testable
val error_testable : Error.t Alcotest.testable
val goal_select_view_testable : Goal_select_view.t Alcotest.testable
val sexp_testable : Sexplib.Sexp.t Alcotest.testable
val reified_goal_testable : string Coq.Goals.Reified_goal.t Alcotest.testable
val vernacexpr_testable : Vernacexpr.vernac_expr Alcotest.testable

val vernac_control_gen_r_testable :
  ( Vernacexpr.control_flag,
    Vernacexpr.synterp_vernac_expr )
  Vernacexpr.vernac_control_gen_r
  Alcotest.testable

val synterp_vernac_expr_testable :
  Vernacexpr.synterp_vernac_expr Alcotest.testable

val testable_nary_tree :
  (Format.formatter -> 'a -> unit) ->
  ('a -> 'a -> bool) ->
  'a nary_tree Alcotest.testable

val expect_ok : context:string -> pp_error:'e Fmt.t -> ('a, 'e) result -> 'a
val expect_some : context:string -> 'a option -> 'a
val expect_single : context:string -> pp:'a Fmt.t -> 'a list -> 'a
val expect_nth : context:string -> pp:'a Fmt.t -> int -> 'a list -> 'a
val expect_head : context:string -> 'a list -> 'a
val expect_error : context:string -> ('a, 'e) result -> 'e
val expect_nth_default : int -> 'a list -> 'a
val expect_result_ok : ?context:string -> ('a, Error.t) result -> 'a
val check_list_unique : eq:('a -> 'a -> bool) -> pp:'a Fmt.t -> 'a list -> unit
val check_list_sorted : cmp:('a -> 'a -> int) -> pp:'a Fmt.t -> 'a list -> unit
