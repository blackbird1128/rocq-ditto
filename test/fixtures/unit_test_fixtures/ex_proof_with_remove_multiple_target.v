Lemma ex_and: forall P: Prop, P ->  P /\ P.
Proof.
  intros.
  split.
  auto;easy.
  auto;easy.
Qed.
