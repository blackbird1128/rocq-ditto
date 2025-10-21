Require Import Lia.

Lemma l: forall A : Prop, A ->  A /\ A.
Proof.
  intros;
  (split;
     [ induction n;   [ induction n; [ reflexivity | simpl; (rewrite IHn; reflexivity) ]     | reflexivity ]   | lia ]).
Qed.
