Require Arith.

Lemma l: forall n: nat, n * 1 = n /\ 1 * n = n.
Proof.
  intros.
  split.
  assert (H: n + 0 = n) by (idtac;auto with arith);auto with arith.
  induction n.
  reflexivity.
  simpl (1 * S n).
  auto.
Qed.
