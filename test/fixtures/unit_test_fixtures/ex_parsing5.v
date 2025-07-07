(* this is just filled with comments *)
(* we should be able to rewrite the same file  *)
(* nested comments woah (*here it is*) *)
(* multiple lines comment
1 line
2 line
 *)

Theorem modus_ponens: 
  forall A B: Prop, A /\ (A -> B) -> B.
Proof.
  intros.
  apply H.
  destruct H as [H1 H2].
  assumption.
Qed.


(* some more comments *)
