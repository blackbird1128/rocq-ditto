
Lemma foo: forall A: Prop, A ->  A.
Proof.
  intros A H.
  assert (H0 : A -> A /\ A).
  auto.
  auto.
Qed.
