
Lemma a_and_a: forall A, A /\ A ->  A.
Proof.
  intros.
  induction H.
  assumption.
Qed.
