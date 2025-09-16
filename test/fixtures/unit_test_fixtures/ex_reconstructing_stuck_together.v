Lemma a:forall n:nat,n*0=0.
Proof.
induction n.
-reflexivity.
-simpl.
rewrite IHn.
reflexivity.
