
Theorem modus_ponens: (*  embedded comment *)
  forall A B: Prop, A /\ (A -> B) -> B.
Proof. (* some other comments *)
  intros. (* a comment *)
  apply H. (* on each line *)
  destruct H as [H1 H2]. (*create some trouble *)
  assumption. 
Qed.
