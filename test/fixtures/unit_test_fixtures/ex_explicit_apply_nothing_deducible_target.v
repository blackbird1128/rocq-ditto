
Lemma foo : forall P Q : Prop, P -> Q -> P /\ Q.
Proof.
  intros P Q HP HQ.
  assert (P /\ Q).
  apply conj; [ exact HP | exact HQ ].
  exact H.
Qed.
