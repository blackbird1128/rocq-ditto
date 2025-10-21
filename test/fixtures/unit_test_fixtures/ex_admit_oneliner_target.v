Lemma foo : forall A B C: Prop, A/\B/\C -> A/\B/\C.
Proof.
intros.
decompose [and] H.
repeat split.
admit.
admit.
Admitted.
