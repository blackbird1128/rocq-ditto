Definition Foo A B C := A \/ B \/ C.

Lemma foo_foo : forall A B C : Prop, Foo A B C -> Foo C B A.
Proof.
  intros.
  lazy delta [Foo].
  unfold Foo in *.
  tauto.
Qed.
