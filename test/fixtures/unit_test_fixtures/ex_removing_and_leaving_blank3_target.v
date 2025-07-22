Theorem modus_ponens: 
  forall A B: Prop, A /\ (A -> B) -> B.
Proof.
  intros.
  apply H.                        assumption.
Qed.
