Require Import Lia.

Fixpoint fact (n : nat) : nat :=
  match n with
  | 0 =>  1
  | S n =>  S n * fact n
  end.

Notation "n !" := (fact n) (at level 50).

Theorem fact_pos : forall n : nat, n! > 0.
Proof.
  induction n.
  - { simpl. lia. }
  - { simpl. lia. }
Qed.
