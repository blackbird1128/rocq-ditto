
Lemma example : forall n : nat, n  + 0 =  0 + n.
Proof.
  intros.
  Search "stuff".
  induction n. (*********************)
  reflexivity.
  simpl. (*****)
  rewrite IHn.
  simpl.
  reflexivity.
Qed.


Compute 1 + 1.

Lemma example2 : forall n : nat, n * 1 = n.
Proof. (* comment here *)
  induction  n.
  simpl.
  reflexivity.
  simpl. (* more comments *)
  rewrite IHn.
  reflexivity.
Qed.
