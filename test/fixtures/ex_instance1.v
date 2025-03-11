
Class Eq (A : Type) := {
  eqb : A -> A -> bool;
  eqb_refl : forall x, eqb x x = true
}.

Instance EqNat : Eq nat.
Proof.
  refine {|
    eqb := Nat.eqb;
  |}.
  (* Now we must prove eqb_refl *)
  
  intros x.
  induction x.
  simpl.
  reflexivity.
  simpl.
  apply IHx.
Qed.
