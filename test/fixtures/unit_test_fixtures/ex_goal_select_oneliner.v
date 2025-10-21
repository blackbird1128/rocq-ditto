Require Import Lia.

Lemma l: forall n : nat, n * 1 = n /\ n + n = 2 * n.
Proof.
  intros.
  split.
  2:induction n.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
  reflexivity.
  lia.
Qed.
