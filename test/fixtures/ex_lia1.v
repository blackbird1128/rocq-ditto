Require Import Lia.

Lemma add_zero: forall n : nat, n + 0 = n.
Proof.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.
