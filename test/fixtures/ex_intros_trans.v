
Theorem modus_ponens:
  forall A B: Prop, A /\ (A -> B) -> B.
Proof.
  intros.
  Search "nothing".
  destruct H as [H1 H2].
  apply H2.
  Search "stuff".
  assumption.
Qed.

Compute 1.
Compute 2.
