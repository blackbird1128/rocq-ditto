Definition eq_nat_dec (n m : nat) : {n = m} + {n <> m}.
Proof.
  revert m.
  induction n as [|n IH]; destruct m; try (right; congruence).
  - left. reflexivity.
  - destruct (IH m); [left; congruence | right; congruence].
Defined.
