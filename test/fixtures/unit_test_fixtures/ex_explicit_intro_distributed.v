From Coq Require Arith.

Lemma foo (n m : nat) :
  (forall x : nat, x = x) /\ (forall y : nat, y = y).
Proof.
  split; intro; reflexivity.
Qed.
