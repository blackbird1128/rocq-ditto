
Lemma use_hyp_auto : forall (P Q R : Prop), P -> (P -> Q) -> (Q -> R) -> R.
Proof.
  auto.
Qed.
