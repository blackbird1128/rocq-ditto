Require Import Coq.Arith.Arith.
Require Import Recdef.

Function div2 (n : nat) {measure id n} : nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | S (S p) => S (div2 p)
  end.
Proof.
  intros n m H.
  simpl.
  inversion H; subst.
  auto with arith.
  auto with arith.
Qed.

