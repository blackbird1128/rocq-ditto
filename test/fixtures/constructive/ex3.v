
Lemma lm : forall n : nat, n + 0 = n.
Proof.
  intros.
  assert (exists m: nat, m = n +1) by eauto.
  auto.
Qed.
