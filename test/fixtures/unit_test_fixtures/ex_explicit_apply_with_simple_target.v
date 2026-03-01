
Lemma lemma_two : forall A B : Prop, A -> B -> A.
Proof.
  intros A B a b.
  exact a.
Qed.

Lemma foo : forall P Q : Prop, P -> Q -> P.
Proof.
  intros P Q HP HQ.
  apply (lemma_two P P); exact HP.
Qed.
