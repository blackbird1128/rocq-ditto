Require Import Lists.List.
Import ListNotations.

Fixpoint filter {A: Type} (l: list A) (f: A -> bool) : list A :=
  match l with
    | [] => []
    | x::tail => if f x then x :: filter tail f else filter tail f
  end.

Lemma use_hyp_auto : forall (P Q R : Prop), (P -> (P -> Q) -> (Q -> R) -> (R/\Q)) /\(P -> (P -> Q) -> (Q -> R) -> (R/\Q)) .
Proof.
  intros.
  split.
  auto.
  intros.
  auto.
Qed.

Lemma filter_idempotent: forall A: Type, forall l: list A, forall f: A -> bool, filter (filter l f) f = filter l f.
Proof.
  intros.
  induction l.
  simpl.
  reflexivity.
  destruct (f a) eqn:Ia.
  simpl.
  rewrite Ia.
  simpl.
  rewrite Ia.
  rewrite IHl.
  reflexivity.
  simpl.
  rewrite Ia.
  rewrite IHl.
  reflexivity.
Qed.
