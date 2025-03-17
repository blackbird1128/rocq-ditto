

Module B.
  Definition a := 0.
End B.

Module A.
  Lemma a: forall n : nat, n + 0 = n.
  Proof.
    intros.
    auto.
  Qed.

End A.
