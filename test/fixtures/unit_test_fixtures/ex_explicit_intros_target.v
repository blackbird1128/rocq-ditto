From Coq Require Arith.

Lemma foo:
  forall n: nat, n * 1 = n.
Proof.
  intros n.
  auto with arith.
Qed.
