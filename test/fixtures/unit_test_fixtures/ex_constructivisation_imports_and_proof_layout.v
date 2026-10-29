Ltac solve_dec := exact I.

Lemma inline_dec : True.
Proof. exact I. Qed.

Lemma mixed_dec : True.
Proof. exact I.
Qed.

Lemma multiline_dec : True.
Proof.
  exact I.
Qed.

Lemma admitted_dec : True.
Admitted.

Lemma transparent_dec : True.
Proof. exact I. Defined.
