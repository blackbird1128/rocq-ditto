Theorem modus_ponens:
  forall A B: Prop, A /\ (A -> B) -> B.
Proof.
  intro.
  intro.
  intro.
  destruct H as [H1 H2]. 
  apply H2.
  assumption.
Qed.
