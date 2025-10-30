Lemma foo : forall n :nat, n + 0 = n. 
Proof.
induction n as [|n IHn];
  [ reflexivity
  | match goal with
    | id:n + 0 = n |- _ => revert id
    end; (simpl; (intros; (rewrite IHn; reflexivity))) ].
Qed.
