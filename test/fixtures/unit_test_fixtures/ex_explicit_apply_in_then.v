Lemma thm : forall P : Prop, P -> P.
Proof.
  intros P HP.
  exact HP.
Qed.

Lemma foo : forall A : Prop, A -> A.
Proof.
  intros; apply thm; assumption. 
Qed.
