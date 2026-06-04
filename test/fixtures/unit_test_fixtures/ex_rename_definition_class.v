Class Foo_theory
  (Tpoint : Type)
  (Foo : Tpoint -> Tpoint -> Tpoint -> Tpoint -> Prop) :=
{
  foo_refl : forall A B, Foo A B A B;
  foo_left_comm : forall A B C D, Foo A B C D -> Foo B A C D;
}.
