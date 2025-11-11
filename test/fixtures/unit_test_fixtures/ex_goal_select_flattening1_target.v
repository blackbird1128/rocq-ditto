Require Import Lia.

Lemma l: forall n : nat, n * 1 = n /\ n + n = 2 * n.
Proof.
  intros.
  split.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
  induction n.
  reflexivity.
  lia.
Qed.
