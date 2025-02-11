
(* comment *)

Lemma example : forall n : nat, n  + 0 =  0 + n.
Proof.
  intros.
  Search "stuff". (* comment on useless line *)
  induction n. (************************************************************)
  reflexivity.
  simpl. (* comment here *)
  Search "aaa". (*useless comment *)
  rewrite IHn.
  simpl. (************************************************************)
  reflexivity.
Qed.  

(**********************************************)
Compute 2 + 3.
(**********************************************)
Lemma example2 : forall n : nat, n * 1 = n.
Proof. (* comment here *)
  induction  n.
  simpl.
  reflexivity.
  simpl. (* more comments *)
  rewrite IHn.
  reflexivity.
Qed.

Lemma ex3: forall n : nat, n * 0 = 0.
Proof.
  intros.
  induction n.
  simpl.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.
