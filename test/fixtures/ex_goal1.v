Require Import Lia.

Goal forall n : nat, 0 + n = n + 0.
Proof.
  induction n.
  1-2:lia.
Qed. 
