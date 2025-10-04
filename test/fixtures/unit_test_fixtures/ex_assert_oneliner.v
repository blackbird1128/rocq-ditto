Require Import Arith.

Lemma n_times_one_bis: forall n: nat, n * 1 = n /\ 1 * n = n.
Proof.
  intros.
  split.
  assert (H : S n <= S (S n)) by auto with arith; idtac.
  auto with arith.
  auto with arith.
Qed.
  


     
