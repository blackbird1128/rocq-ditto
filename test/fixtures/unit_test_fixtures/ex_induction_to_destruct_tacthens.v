
Lemma b_eq_b: forall b : bool, b = b.
Proof.
  intros.
  induction b; [reflexivity | reflexivity].
Qed.
