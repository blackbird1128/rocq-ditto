
Lemma a: forall A B : Prop, A ->  B ->  (A /\ B).
Proof.
  intros.
  split.
  assumption.
  assumption.
Qed.
