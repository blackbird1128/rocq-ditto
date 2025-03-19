
Lemma use_hyp_auto : forall (P Q R : Prop), (P -> (P -> Q) -> (Q -> R) -> (R/\Q)) /\(P -> (P -> Q) -> (Q -> R) -> (R/\Q)) .
Proof.
  intros.
  split.
  intro.
  intro.
  intro.
  simple apply conj.
  simple apply H1.
  simple apply H0.
  assumption.
  simple apply H0.
  assumption.
  intros.
  tauto. (* only test the first auto *)
Qed.
