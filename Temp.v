Require Import Arith Lia Lists.List Logic.ConstructiveEpsilon.
Require Import Coq.ZArith.Znumtheory.
Definition Witness := constructive_indefinite_ground_description_nat.

Notation "x '<d' y" := ( exists k, x*k = y ) (at level 30).
Definition irred (p : nat) := p > 1 /\ forall n, n < p -> n <d p -> n = 1.
Definition list_prod l := fold_right mult 1 l.


Lemma irred_factor n :
  n > 1 -> { q | irred q /\ q <d n}.
Proof.
  intros Hn. apply Witness.
  - intros ?. admit.
  -   
Admitted.

Definition factorization (n : nat) : n <> 0 ->
  { l : list nat | n = list_prod l /\ Forall irred l }.
Proof. 
  intros Hn.
  induction n as [n rec] using lt_wf_rect.
  destruct n as [|[|n]]; try tauto.
  - exists nil; auto.
  - assert (H: S (S n) > 1) by lia.
    destruct (irred_factor _ H) as (q & irred_q & [x Hx]%Witness).
    destruct (rec x) as (lx & Hlx & ?).
    + destruct x, q, irred_q; lia.
    + lia.
    + exists (q :: lx). split.
      * now rewrite <-Hx, Hlx.
      * now constructor.   
    + intros ?. decide equality.
Qed.

