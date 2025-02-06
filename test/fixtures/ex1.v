
Ltac t x := exists x; reflexivity.


Theorem a: exists n, n=0.
Proof.
  t 0.
Qed.
                
                

Theorem modus_ponens: 
  forall A B: Prop, A /\ (A -> B) -> B.
Proof.
  intros.
  destruct H as [H1 H2].
  apply H2.
  assumption.
Qed.


