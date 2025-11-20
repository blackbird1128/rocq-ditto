Require Import ssreflect.


Lemma before: forall n: nat, n * 0 = 0.
Proof.
intros.
induction n.
by reflexivity.
simpl.
by rewrite IHn.
Qed.

Lemma foo : forall n:nat, True.
Proof.
move => n.
have: (n=n) by rewrite /=.
move => Hn //.
Qed.

Lemma after: forall P: Prop, P -> P.
Proof.
intros.
assumption.
Qed.
