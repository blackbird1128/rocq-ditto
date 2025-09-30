Lemma plus_n : forall n : nat, (n + 0) = n.
Proof.
induction n.
Check bool.
reflexivity.
Search nat.
simpl.
rewrite IHn.
reflexivity.
Qed.
