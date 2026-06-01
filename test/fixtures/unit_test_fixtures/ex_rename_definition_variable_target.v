
Section Test.

Variable (Bar : Prop -> Prop -> Prop -> Prop).

Lemma foo_foo : forall A B C : Prop, Bar A B C -> Bar A B C.
Proof.
  intros.
  assumption.
Qed.

End Test.
