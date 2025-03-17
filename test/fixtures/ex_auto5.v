Goal forall P Q R S : Prop, 
  (P -> Q) -> (Q -> R) -> (R -> S) -> (P \/ Q) -> ((Q /\ P) \/ (P \/ R) ).
Proof.
  intros.
  destruct H2.
  info_auto.
  info_auto.
Qed.
