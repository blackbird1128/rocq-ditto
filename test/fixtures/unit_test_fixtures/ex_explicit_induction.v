
Lemma foo: forall n : nat, n * 1 = n.
Proof.
  intros n.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.
