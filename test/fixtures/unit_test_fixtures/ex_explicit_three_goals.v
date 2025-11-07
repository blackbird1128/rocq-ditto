
Lemma foo: forall n : nat, n * 1 = n /\ forall A: Prop, A -> A.
Proof.
  split.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn; reflexivity.
  auto.
Qed.
