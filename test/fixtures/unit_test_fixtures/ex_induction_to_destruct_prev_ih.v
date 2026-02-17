
Lemma prev_ih_example: forall n : nat, forall b : bool, b = b.
Proof.
  intros.
  induction n.
  - induction b; reflexivity.
  - induction b; reflexivity.
Qed.
