Require Import Arith.
Require Import Lia.

(* Lemma 1: Addition is associative *)
Lemma add_assoc : forall a b c : nat, a + (b + c) = (a + b) + c.
Proof.
  intros a b c.
  induction a as [| a' IH].
  - (* Base case: a = 0 *)
    simpl.
    reflexivity.
  - (* Inductive step: a = S a' *)
    simpl.
    rewrite IH.
    reflexivity.
Qed.

(* Lemma 2: Addition is commutative *)
Lemma add_comm : forall a b : nat, a + b = b + a.
Proof.
  intros a b.
  induction a as [| a' IH].
  - (* Base case: a = 0 *)
    simpl.
    rewrite Nat.add_0_r.
    reflexivity.
  - (* Inductive step: a = S a' *)
    simpl.
    rewrite IH.
    rewrite Nat.add_succ_r.
    reflexivity.
Qed.

(* Lemma 3: Multiplication is associative *)
Lemma mul_assoc : forall a b c : nat, a * (b * c) = (a * b) * c.
Proof.
  intros a b c.
  induction a as [| a' IH].
  - (* Base case: a = 0 *)
    simpl.
    reflexivity.
  - (* Inductive step: a = S a' *)
    simpl.
    rewrite IH.
    lia.
Qed.

(* Lemma 4: Multiplication is commutative *)
Lemma mul_comm : forall a b : nat, a * b = b * a.
Proof.
  intros a b.
  induction a as [| a' IH].
  - (* Base case: a = 0 *)
    simpl.
    rewrite Nat.mul_0_r.
    reflexivity.
  - (* Inductive step: a = S a' *)
    simpl.
    rewrite IH.
    rewrite add_comm.
    lia.
Qed.

(* Lemma 5: Distributive property of multiplication over addition *)
Lemma mul_add_distr : forall a b c : nat, a * (b + c) = a * b + a * c.
Proof.
  intros a b c.
  induction a as [| a' IH].
  - (* Base case: a = 0 *)
    simpl.
    reflexivity.
  - (* Inductive step: a = S a' *)
    simpl.
    rewrite IH.
    rewrite add_assoc.
    lia.
Qed.

(* Theorem: Multiplication distributes over addition and is commutative and associative *)
Theorem arithmetic_properties : forall a b c : nat,
  a + b = b + a /\
  a * b = b * a /\
  a * (b + c) = a * b + a * c /\
  a + (b + c) = (a + b) + c /\
  a * (b * c) = (a * b) * c.
Proof.
  intros a b c.
  split.
  - (* First subgoal: a + b = b + a *)
    apply add_comm.
  - split.
    + (* Second subgoal: a * b = b * a *)
      apply mul_comm.
    + split.
      * (* Third subgoal: a * (b + c) = a * b + a * c *)
        apply mul_add_distr.
      * split.
        -- (* Fourth subgoal: a + (b + c) = (a + b) + c *)
           apply add_assoc.
        -- (* Fifth subgoal: a * (b * c) = (a * b) * c *)
           apply mul_assoc.
Qed.

