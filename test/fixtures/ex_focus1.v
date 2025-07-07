
Theorem th: forall n : nat, n * 1 = n.
Proof.
  intros.
  induction n.
  Focus.
  Unfocus.
  Focus.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.
