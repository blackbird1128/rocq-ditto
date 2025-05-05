
Theorem th : forall n : nat,
n + 0 = n.
Proof.
  intros.
  induction n.
  Compute 1 +
  2 + 3 + 4
  + 5 + 6.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.
