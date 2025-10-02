Lemma foo : forall n:nat, n+0=n.
Proof.
induction n.
reflexivity.
simpl.
try (rewrite IHn in *).
reflexivity.
Qed.
