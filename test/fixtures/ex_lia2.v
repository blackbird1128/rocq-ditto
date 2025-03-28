Require Import Lia.

Lemma split_lia: forall n : nat,forall P : Prop, (n + n = 2 * n) /\  (P -> P).
Proof.
  intros.
  split.
  induction n.
  reflexivity.
  replace( 2 * S n) with (2 * (n+ 1)) by auto with arith.
  replace (S n + S n) with (( n + n) + 2) by lia.
  lia.
  auto.
Qed.  
