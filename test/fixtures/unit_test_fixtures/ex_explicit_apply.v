Lemma lemma_two : forall A B : Prop, A -> B -> A.
Proof. intros A B a b. exact a. Qed.

Lemma foo (A B : Prop) : A -> B -> A.
Proof.
  apply lemma_two.
Qed.
