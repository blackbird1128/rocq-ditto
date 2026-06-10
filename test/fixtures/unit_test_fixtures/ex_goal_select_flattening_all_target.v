
Lemma foo: True \/ True \/ True ->  True.
Proof.
  intros.
  decompose [or] H.
  tauto.
  tauto.
  tauto.
Qed.
