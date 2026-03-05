
Lemma a: forall n m : nat, n = m -> m = n.
Proof.
  intros n m H.
  apply eq_sym.
  exact H.
Qed.
