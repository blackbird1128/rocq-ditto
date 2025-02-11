
Theorem modus_ponens: 
  forall A B: Prop, A /\ (A -> B) -> B.
Proof.
  assert (A : 0 + 0 = 0) by reflexivity.
  intros.
  apply H.
  destruct H as [H1 H2].
  assumption.
Qed.
