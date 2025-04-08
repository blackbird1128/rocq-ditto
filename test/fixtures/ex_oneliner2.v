Lemma foo : forall A B C : Prop, A \/ ( B /\ C) -> (A \/ B) /\ (A \/ C).
Proof.
intros; destruct H.
split.
left; assumption.
left; assumption.
destruct H.
split.
right; assumption.
right; assumption.
Qed.
