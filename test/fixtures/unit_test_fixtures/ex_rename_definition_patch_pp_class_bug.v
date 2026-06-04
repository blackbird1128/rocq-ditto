(* This test check that we correctly return a valid VernacInduction even after the bugged pretty printing found in version <= 9.2.0. *)
(* To do this, we need to force the pretty printer of pr_record_field to take the happy path by explicitly typing the return type of DefExpr *)
(* Even if this doesn't change the result much, this is a hack that should be removed when the bug is fixed *)

Class FooClass :=
{
  Point : Type;
  Foo: Point ->  Point ->  Point ->  Point ->  Prop;  
  eq := @eq Point;
  neq A B := ~ eq A B;
}.
