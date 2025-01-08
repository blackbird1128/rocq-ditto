Require Import Lia.
Require Import Arith.

Lemma test: forall n : nat, n * 2 = n + n.
Proof.
  intros.
  induction n.
  simpl.
  reflexivity.
  simpl.
  rewrite IHn.
  lia.
Qed.


Fixpoint factorial n :=
  match n with
  | 0 => 1
  | S m => n * factorial m
  end.

Lemma fact_n_plus_one : forall n : nat,  factorial (n + 1) = (n +1) * factorial n. 
Proof.
  intros.
  induction n.
  simpl.
  reflexivity.
  simpl.
  rewrite IHn.
  lia.
Qed.
  
