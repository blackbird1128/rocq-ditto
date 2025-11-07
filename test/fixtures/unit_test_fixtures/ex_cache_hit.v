

Fixpoint fact (n : nat) :=
  match n with
  | 0 => 1
  | S n' => n * fact n'
  end.

Lemma a: fact 9 = fact 8 * 9.
Proof.
  compute. reflexivity.
Qed.

Lemma b: fact 8 = fact 7 * 8.
Proof.
  compute. reflexivity.
Qed.

Lemma c: fact 7 = fact 6 * 7.
Proof.
  compute. reflexivity.
Qed.
