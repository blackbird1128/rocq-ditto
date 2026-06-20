Definition Foo A B C := A \/ B \/ C.

Ltac fizz t := unfold t in *.

Lemma foo_foo: forall A B C : Prop, Foo A B C -> Foo C B A.
Proof.
  intros.
  fizz Foo.
  tauto.
Qed.
