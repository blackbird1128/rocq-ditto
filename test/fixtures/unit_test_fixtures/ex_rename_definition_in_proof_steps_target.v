Definition Bar A B C := A \/ B \/ C.

Lemma foo_foo: forall A B C : Prop, Bar A B C -> Bar C B A.
Proof.
  intros.
  unfold Bar in *.
  tauto.
Qed.
