Lemma f : forall x:Prop, True -> True.
Proof.
intros; assumption.
Qed.
  
Require Arith.

Lemma addnC n : n + 0 = n.
Proof.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Lemma addnC' n : n + 0 = n.
Proof.
  { induction n.
    { reflexivity. }
    { simpl. rewrite IHn. reflexivity. }
  }
Qed.

Lemma addnC_opt n : n + 0 = n.
Proof.
  induction n; [ reflexivity | simpl; rewrite IHn; reflexivity]. 
Qed.
