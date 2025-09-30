Lemma plus_n : forall n : nat, (n + 0) = n.
Proof.
induction n; [ reflexivity | simpl; rewrite IHn; reflexivity ].
Qed.
