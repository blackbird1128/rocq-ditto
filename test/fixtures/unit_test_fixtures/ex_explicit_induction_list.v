Require Import Coq.Lists.List.
Import ListNotations.

Lemma rev_injective : forall (A : Type) (la lb : list A),
  rev la = rev lb -> la = lb.
Proof.
  intros A la lb H.
  induction la.
  inversion H.
  rewrite H1.
  rewrite <- H.
  rewrite H1.
  now rewrite rev_involutive.
  inversion H.
  replace (a :: la) with (rev (rev (a::la))) by (now rewrite rev_involutive).
  rewrite H.
  now rewrite rev_involutive.
Qed.
