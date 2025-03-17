
Lemma working_of_auto_1 : forall (P : nat -> Prop),
    (forall k, P (k - 1) -> P k) ->
    P(0) ->  (forall k, P (k + 1) -> P k) ->
    (P 3).
Proof.
  intro.
  intro.
  intro.
  info_auto 4.
Qed.
