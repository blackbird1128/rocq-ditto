
Lemma working_of_auto_1 : forall (P : nat -> Prop),
    (forall k, P (k - 1) -> P k) ->
    P(0) ->  (forall k, P (k + 1) -> P k) ->
    (P 2).
Proof.
  intro.
  intro.
  intro.
  info_auto 3.
Qed.

(*
intro.
simple apply H1.
 simple apply H1.
  simple apply H1.
  simple apply H.
 simple apply H.
  simple apply H1.
  simple apply H.
simple apply H.
 simple apply H1.
  simple apply H1.
  simple apply H.
 simple apply H.
  assumption.
 *)

(* solution :

intro.
simple apply H.
simple apply H.
assumption.


*)


(* algorithm: backtracking

solution:

solve_fold:
 cur_state: top_stack
 if num_children = 0:
  if num_goal < prev_goal then
    acc
  else
    pop_until_prev_branch
 else:
   new_state
   put new_state_on_top

  



*)


Goal forall P Q R S : Prop, 
  (P -> Q) -> (Q -> R) -> (R -> S) -> (P \/ S) -> (Q \/ R \/ S).
Proof.
  intros P Q R S HPQ QRR RSS H.
  destruct H.
  simple apply or_intror.
  simple apply or_introl.
  simple apply QRR.
   simple apply HPQ.
    assumption.
  info_auto.
  auto.
Qed.


(*
simple apply or_intror.
 simple apply or_intror.
  simple apply RSS.
   simple apply QRR.
    simple apply HPQ.
 simple apply or_introl.
  simple apply QRR.
   simple apply HPQ.
    assumption.
*)

(* solution:

