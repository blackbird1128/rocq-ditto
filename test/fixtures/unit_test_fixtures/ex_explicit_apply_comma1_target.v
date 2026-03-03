Lemma A : forall P Q : Prop, (P -> Q) -> P -> Q.
Proof.
  intros P Q HPQ HP. exact (HPQ HP).
Qed.

Lemma B : forall P : Prop, P -> P.
Proof.
  intros P HP. exact HP.
Qed.

Lemma foo : forall P Q : Prop, (P -> Q) -> P -> Q.
Proof.
  intros P Q HPQ HP.
  apply (A P Q), (B P).
  - exact HPQ.
  - exact HP.
Qed.
