Require Import ZArith.

Lemma auto_example_2: forall x y: nat, x > 3 /\ y > x -> y >= 4.
Proof.
  auto with zarith.
Qed.
  
            
  
