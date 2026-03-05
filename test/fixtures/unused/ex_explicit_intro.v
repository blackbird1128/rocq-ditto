From Coq Require Arith.

Lemma foo:
  forall n: nat, n * 1 = n.
Proof.
  intro.
  auto with arith.
Qed.
