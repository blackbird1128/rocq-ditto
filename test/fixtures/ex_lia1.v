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
    | 0 =>  1
    | S m =>  n * factorial m
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

Lemma fact_growing : forall n : nat, 0 < n ->  factorial n < factorial (n + 1).
Proof.
  induction n.
  intros.
  lia.
  intros.
  inversion H.
  simpl.
  lia.
  rewrite <-  Nat.add_1_r.
  rewrite fact_n_plus_one.
  rewrite fact_n_plus_one.
  apply Nat.mul_lt_mono.
  lia.
  apply IHn.
  lia.
Qed.

  
Lemma fact_monotonicty : forall n m : nat, 0 < n  ->  0 < m ->  n < m ->  factorial n < factorial m.
Proof.
  induction m.
  intros.
  simpl.
  lia.
  intros.
  inversion H1.
  rewrite <-  Nat.add_1_r.
  apply fact_growing.
  lia.
  simpl.
  assert ( H4 : factorial m + m * factorial m = ( m +1) * factorial m) by lia.
  rewrite H4.
  rewrite <- Nat.mul_1_l at 1.
  apply Nat.mul_lt_mono.
  lia.
  apply IHm.
  1-3:lia.
Qed.  

Lemma factorial_grows_faster : forall n, 3 < n ->  2 ^ n < factorial n.
Proof.
  induction n.
  intros.
  lia.
  intros.
  inversion H.
  simpl.
  lia.
  simpl.
  Search ( _ + _ < _ + _).
  apply Nat.add_lt_mono.
  lia. (* we can be ineffective here *)
  replace (2 ^ n + 0) with  (2 ^ n).
  replace ( 2 ^ n ) with ( 1 * (2^n)).
  apply Nat.mul_lt_mono.
  1-4: lia.
Qed.


Lemma factorial_not_zero : forall n : nat,  0 < n ->  0 <> factorial n.
Proof.
  intros.
  induction n.
  lia.
  inversion H.
  simpl; lia.
  simpl.
  lia.
Qed.
