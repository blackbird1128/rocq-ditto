Lemma ex_and: forall P: Prop, P ->  P /\ P.
Proof with easy.
  intros.
  split.
  auto...
  auto...
Qed.
