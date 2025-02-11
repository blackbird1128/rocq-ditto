Lemma example2 : forall n : nat, n * 1 = n.
Proof. (* comment here *)
  induction  n.
  simpl.
  reflexivity.
  simpl. (* more comments *)
  rewrite IHn.
  reflexivity.
Qed.
Compute 1 + 1.
Compute 2 + 2.
