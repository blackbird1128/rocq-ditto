
Lemma b_eq_b: forall b : bool, b = b.
Proof.
  intros.
  destruct b; [ reflexivity | reflexivity ].
Qed.
