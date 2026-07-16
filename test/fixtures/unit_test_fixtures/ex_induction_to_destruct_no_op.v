Lemma n_plus_zero_eq_zero_plus_n : forall n : nat, n + 0 = 0 + n.
Proof.
  intros n.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.
