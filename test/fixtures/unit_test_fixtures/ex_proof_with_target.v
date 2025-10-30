Lemma n_times_one: forall n : nat, n * 1 = n.
Proof.
intros;
 (induction n as [| n IHn];
    [ reflexivity | simpl; (rewrite IHn; (auto; easy)) ]).
Qed.
