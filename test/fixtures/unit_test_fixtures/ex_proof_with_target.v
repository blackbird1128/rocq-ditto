Lemma n_times_one: forall n : nat, n * 1 = n.
Proof.
intros;
induction n;
[reflexivity
| simpl;
rewrite IHn; (auto; easy)].
Qed.
