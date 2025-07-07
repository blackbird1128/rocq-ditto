
Theorem th: forall n : nat, n + 0 = n.
Proof.
  intros.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.
