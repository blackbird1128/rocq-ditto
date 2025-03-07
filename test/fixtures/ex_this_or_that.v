Lemma this_or_that: forall A B : Prop, A \/ B ->  B \/ A.
Proof.
  intros.
  destruct H.
  right.
  assumption.
  left.
  assumption.
Qed.
