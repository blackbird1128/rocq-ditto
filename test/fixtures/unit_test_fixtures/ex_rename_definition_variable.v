
Section Test.

Variable Foo : Prop -> Prop -> Prop -> Prop.

Lemma foo_foo : forall A B C : Prop, Foo A B C -> Foo A B C.
Proof.
  intros.
  assumption.
Qed.

End Test.
