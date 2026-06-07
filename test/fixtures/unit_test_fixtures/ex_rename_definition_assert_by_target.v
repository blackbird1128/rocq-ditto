Definition Bar A B C := A \/ B \/ C.

Lemma foo_foo : forall A B C, Bar A B C -> Bar C B A.
Proof.
  intros.
  assert (Bar C B A) by (unfold Bar in *; tauto).
  assumption.
Qed.
