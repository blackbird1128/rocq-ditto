

Inductive Point : Type := 
  | point : nat -> Point.

Lemma l3_17_mock : forall A B C A' B' P : Point,
  A <> B -> B <> C -> A' <> B' -> A <> A' -> B <> B' ->
  exists Q, A <> Q /\ B <> Q /\ C <> Q.
Proof.
Admitted.
(* Mock:
Lemma l3_17 : forall A B C A' B' P,
  BetL A B C -> BetL A' B' C -> BetL A P A' ->
  exists Q, BetL P Q C /\ BetL B Q B'.
*)
