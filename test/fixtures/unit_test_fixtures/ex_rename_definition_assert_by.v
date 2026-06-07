Definition Foo A B C := A \/ B \/ C.

Lemma foo_foo: forall A B C, Foo A B C ->  Foo C B A.
Proof.
  intros.
  assert (Foo C B A) by (unfold Foo in *; tauto).
  assumption.
Qed.
