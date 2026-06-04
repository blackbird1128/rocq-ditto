Class Foo_theory (Tpoint : Type)
(Bar : Tpoint -> Tpoint -> Tpoint -> Tpoint -> Prop) :=
 {
  foo_refl  : forall A B, Bar A B A B;
  foo_left_comm  : forall A B C D, Bar A B C D -> Bar B A C D
 }.
