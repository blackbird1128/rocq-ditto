Definition Bar A B C := A \/ B \/ C.

Ltac fizz t := unfold t in *.

Lemma foo_foo : forall A B C : Prop, Bar A B C -> Bar C B A.
Proof.
  intros.
  fizz Bar.
  tauto.
Qed.
