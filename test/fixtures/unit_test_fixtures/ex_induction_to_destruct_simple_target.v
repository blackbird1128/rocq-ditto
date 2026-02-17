
Lemma a_and_a: forall A, A /\ A ->  A.
Proof.
  intros.
  destruct H.
  assumption.
Qed.
