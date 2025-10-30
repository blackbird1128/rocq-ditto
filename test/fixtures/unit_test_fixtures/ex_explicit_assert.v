
Lemma foo: forall A: Prop, A ->  A.
Proof.
  intros A H.
  assert (A ->  A /\ A).
  auto.
  auto.
Qed.
