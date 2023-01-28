Require Import Lia.

(*  [Rosser A B] expresses that in the time before a proof
    of A is found, B was not refuted. 
 *)
Definition Rosser (A B : nat -> Prop) :=
  exists w, A w /\ (forall v, v < w -> ~ B v).

Lemma Rosser_trans A B C :
  Rosser A B -> Rosser B C -> Rosser A C.
Proof.
  intros [w [HwA HwB]] [w' [HwB' HwC']].
  enough (~ w' < w) as H.
  - exists w. split; auto.
    intros v Hv. apply HwC'. lia.
  - intros ?%(fun h => HwB _ h). tauto.
Qed.

Lemma Rosser_conj A B :
  Rosser A B /\ Rosser B A ->
  exists w, A w /\ B w /\
    forall v, v < w -> ~ A v /\ ~ B v.
Proof.
  intros [[w1 [HA1 HB1]] [w2 [HB2 HA2]]].
  assert (w1 < w2 \/ w1 = w2 \/ w1 > w2) as [H|[->|H]] by lia.
  - exfalso. now apply HA2 with w1.
  - exists w2. repeat split; auto.
  - exfalso. now apply HB1 with w2.
Qed.

Corollary Rosser_iff A B :
  Rosser A B /\ Rosser B A -> exists w, A w <-> B w.
Proof.
  intros [w Hw]%Rosser_conj. exists w. tauto.
Qed.


(*  [Rosser' A B] expresses that including the time a proof
    of A is found, B was not refuted.
 *)
Definition Rosser' (A B : nat -> Prop) :=
  exists w, A w /\ (forall v, v <= w -> ~ B v).

Lemma Rosser_irrefl' A :
  ~ Rosser' A A.
Proof.
  intros [w [H1 H2]]. now apply H2 with w.
Qed.

Lemma Rosser_trans' A B C :
  Rosser' A B -> Rosser' B C -> Rosser' A C.
Proof.
  intros [w [HA HB]] [w' [HB' HC']].
  assert (w <= w' \/ w >= w') as [H|H] by lia.
  - exists w. split; auto.
    intros v Hv. apply HC'. lia.
  - exfalso. now apply (HB w').
Qed.

Lemma Rosser_disj' (A B : nat -> Prop):
  ~(Rosser' A B /\ Rosser' B A).
Proof.
  intros [[w1 [HA1 HB1]] [w2 [HB2 HA2]]].
  assert (w1 <= w2 \/ w1 >= w2) as [H|H] by lia.
  - now apply HA2 with w1.
  - now apply HB1 with w2.
Qed.