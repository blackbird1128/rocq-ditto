Require Import Arith.

(* Define a number with its proof that it's greater than 0 *)
Definition one_gt_zero : { n : nat | n > 0 }.
Proof.
  exists 1.           (* Provide the witness *)
  auto.
Defined.
