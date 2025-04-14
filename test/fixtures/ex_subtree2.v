
Theorem th: forall n : nat, n + 0 = n.
Proof.
  intros.
  rewrite plus_n_O.
  reflexivity.
Qed.
