Lemma foo : forall n :nat, n + 0 = n. 
Proof.
  induction n;
  [ reflexivity
   |  match goal with
     | id:n + 0 = n |- _ => revert id
     end].
Qed.
