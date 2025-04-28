
Inductive Point : Type := 
  | point : nat -> Point.

Lemma point_construction_different : forall A B : Point,
  A <> B ->
  exists C : Point, A <> C /\ B <> C.
Proof.
Admitted.
(* Mock:
Lemma point_construction_different : forall A B,
  exists C, BetL A B C /\ B <> C.
*)



  
  
