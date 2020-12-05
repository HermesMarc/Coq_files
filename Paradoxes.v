
(* Comments between (*** *) are quotations from an indicated source *)

Section Yablo.

(* Taken from: A Universal Approach to Self-ReferentialParadoxes, Incompleteness and Fixed Points *)

(*** There is a belief that all paradoxes would melt away if there were noself-referential statements. Yablo’s Non-self-referential Liar’s Paradox wasformulated counteract that thesis. There is a sequence of statements suchthat none of them ever refer to themselves and yet they are allboth trueand false. Consider the sequence *)

(*** S_i ≡ for all k > i, S_k is untrue *)

(*** Suppose S_n is true for some n. Then S_(n+1) is false as are all subsequent statements. Since all subsequent statements are false, S_(n+1) is true which is a contradiction. So in contrast, S_n is false for all n. That means that S_1 is true and S_2 is true etc etc. Again we have a contradiction. *)


(* In Coq *)

(* The definition of S_i as an inductive predicate fails because of the strict positivity restriction. *)

(* 
Inductive P : nat -> Prop :=
C i : (forall k, i < k -> ~ P k) -> P i. 
 *)


(* If we assume a predicate togehter with its breaking property and replicate the above proof, we get *)

Require Import Lia.

Variable P : forall n : nat, Prop.
Hypothesis HP : forall i, P i <-> (forall k, k > i -> ~P k).

Lemma Y1 : ~(exists n, P n).
Proof.
    intros [n H].
    assert (~ P (S n)).
    - rewrite HP in H.  apply H. auto.
    - apply H0. rewrite HP in *. intros k ?.
      apply H. lia.    
Qed.


Lemma Y2 : ~(forall n, ~ P n).
Proof.
    intros H.
Admitted.

(* Which would now derive False if we also assume e.g. LEM *)


End Yablo.

