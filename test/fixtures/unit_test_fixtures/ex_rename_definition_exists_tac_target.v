Definition Bar A B C := A \/ B \/ C.

Definition Feed A1 B1 C1 := Bar A1 B1 C1 \/ Bar C1 B1 A1.

Lemma foo_feed : forall A B C, A \/ B \/ C ->  exists D E F, Feed D E F.
Proof.
  intros.
  repeat exists (Bar A B C).
  unfold Feed, Bar.
  tauto.
Qed.
