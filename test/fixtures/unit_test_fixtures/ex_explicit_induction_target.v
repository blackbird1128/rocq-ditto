
Lemma foo: forall n : nat, n * 1 = n.
Proof.
  intros n.
  induction n as [| n IHn].
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.
