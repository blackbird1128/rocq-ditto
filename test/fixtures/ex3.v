Require Import Arith.

Lemma and_split:
  forall A B : Prop, A /\ B ->  B /\ A.
Proof.
  intros.
  split.
  destruct H as [H1 H2].
  assumption.
  destruct H as [H1 H2].
  assumption.
Qed.

Lemma and_split_bis:
  forall A B : Prop, A /\ B -> (B/\A)/\(A/\B).
Proof.
  intros.
  destruct H as [H1 H2].
  split.
  split.
  assumption.
  assumption.
  split.
  assumption.
  assumption.
Qed.
  
  
