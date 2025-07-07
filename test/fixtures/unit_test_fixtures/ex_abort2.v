Require Import Lia.

Lemma example: forall n : nat, n + 0 = n.
Proof.
  induction n  .
Abort.

Compute 21 * 2.

Lemma example2: forall n : nat, n + 1 = 1 + n.
Proof.
  induction n.
  lia.  
  lia.
Qed.

  
