Definition Bar A B C := A \/ B \/ C.

Lemma foo_foo : forall A B C : Prop, Bar A B C -> Bar C B A.
Proof.
  intros.
  cbv delta [Bar].
  unfold Bar in *.
  tauto.
Qed.
