From Coq Require Import List.
Import ListNotations.

Declare Scope uni.
Delimit Scope uni with uni.

Notation "¬ P" := (~ P) (at level 75) : uni.
Notation "P ∧ Q" := (P /\ Q) (at level 80) : uni.
Notation "P ∨ Q" := (P \/ Q) (at level 85) : uni.
Notation "P → Q" := (P -> Q) (at level 99) : uni.
Notation "∀ x , P" := (forall x, P) (at level 200) : uni.
Notation "∃ x , P" := (exists x, P) (at level 200) : uni.

Notation "λ x , t" := (fun x => t) (at level 200) : uni.
Notation "A → B" := (A -> B) (at level 99, right associativity) : type_scope.

Notation "x ∷ xs" := (cons x xs) (at level 60, right associativity) : list_scope.
Notation "∅" := (@nil _) : list_scope.

Open Scope uni.
Open Scope list_scope.


Lemma demo : forall P Q: Prop, P ∧ Q → Q ∧ P.
Proof.
  intros.
  destruct H.
  split; auto.
Qed.
