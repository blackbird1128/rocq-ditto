
Lemma lemma_two : forall A B : Prop, A -> B -> A.
Proof.
  intros A B a b.
  exact a.
Qed.

Lemma foo : forall P Q : Prop, P -> Q -> P.
Proof.
  intros P Q HP HQ.
  assert (P -> Q -> P) by apply lemma_two.
  exact (H HP HQ).
Qed.
