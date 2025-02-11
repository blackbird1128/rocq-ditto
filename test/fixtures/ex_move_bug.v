Theorem modus_ponens: 
  forall A B: Prop, A /\ (A -> B) -> B.
Proof.
  intros.
  apply H. (**********)
  destruct H as [H1 H2].
  assumption. 
Qed.
Compute 1.
Theorem modus_ponens_bis: 
  forall A B: Prop, A /\ (A -> B) -> B.
Proof.
  intros A B H.
  apply H.
  destruct H as [H1 H2].
  assumption.
Qed.
