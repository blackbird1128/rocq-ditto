
Lemma use_hyp_auto : forall (P Q R : Prop), (P -> (P -> Q) -> (Q -> R) -> (R/\Q)) /\(P -> (P -> Q) -> (Q -> R) -> (R/\Q)) .
Proof.
  intros.
  split.
  auto.
  intros.
  tauto. (* only test the first auto *)
Qed.
