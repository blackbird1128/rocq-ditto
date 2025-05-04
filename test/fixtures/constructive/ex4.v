
Definition f x := x + 1.

Definition g_long x := x + 1.

Lemma f_eq : forall n : nat, f n = n + 1.
Proof.
  intros.
  reflexivity.
Qed.
