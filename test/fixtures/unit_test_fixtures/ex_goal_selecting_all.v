
Lemma foo: True \/ True \/ True ->  True.
Proof.
  intros.
  decompose [or] H.
  all:tauto.
Qed.
