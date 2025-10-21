Lemma foo : forall n:nat, plus n 0 = n.
Proof.
induction n; [ reflexivity | simpl; (rewrite IHn; reflexivity) ].
Qed.
