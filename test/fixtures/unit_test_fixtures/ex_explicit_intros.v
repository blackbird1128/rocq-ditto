
Lemma foo:
  forall n: nat, n * 1 = n.
Proof.
  intros.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.
  
