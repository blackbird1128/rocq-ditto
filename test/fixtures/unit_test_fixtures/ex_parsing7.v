Theorem modus_ponens: (** embedded comment *)
  forall A B: Prop, A /\ (A -> B) -> B.
Proof.
  intros. (*in the same line comment*)
  destruct H as [H1 H2]. 
  apply H2.
  assumption.
Qed.

(**weird comment*)
