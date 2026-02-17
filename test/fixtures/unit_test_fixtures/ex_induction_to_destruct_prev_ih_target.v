
Lemma prev_ih_example: forall n : nat, forall b : bool, b = b.
Proof.
  intros.
  induction n.
  - destruct b; reflexivity.
  - destruct b; reflexivity.
Qed.
