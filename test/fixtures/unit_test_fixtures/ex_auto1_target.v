
Lemma use_hyp_auto : forall (P Q R : Prop), P -> (P -> Q) -> (Q -> R) -> R.
Proof.
  intro.
  intro.
  intro.
  intro.
  intro.
  intro.
  simple apply H1.
  simple apply H0.
  assumption.
Qed.
