
Goal forall P Q R S : Prop, 
  (P -> Q) -> (Q -> R) -> (R -> S) -> (P \/ S) -> (Q \/ R \/ S).
Proof.
  intros P Q R S HPQ QRR RSS H.
  destruct H.
  auto.
  auto.
Qed.
