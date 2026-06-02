Definition Foo A B C := A \/ B \/ C.

Definition Feed A1 B1 C1 := Foo A1 B1 C1 \/ Foo C1 B1 A1.

Lemma foo_feed : forall A B C, A \/ B \/ C ->  exists D E F, Feed D E F.
Proof.
  intros.
  repeat (exists (Foo A B C)).
  unfold Feed, Foo.
  tauto.
Qed.
