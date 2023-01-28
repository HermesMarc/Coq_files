Require Import Arith Lia.
Load Preamble.

(* Division with Rest *)

Module Euclid.
Definition uniqueness d x q r := 
  forall q' r', r' < d -> x = q'*d + r' -> q' = q /\ r' = r.   

Tactic Notation "assume_first" :=
  match goal with
  | H : _ |- ?A /\ ?B => 
    refine (
      (fun f a => conj a (f a)) (fun _ => _) _
    )
  end.

Definition Euclid d x :
  Sigma q r,
      x = q*d + r
  /\ (0 < d <-> r < d)
  /\ uniqueness d x q r.
Proof.
  destruct d as [|d].
  exists 0, x. repeat split; lia.
  induction x as [|x IH].
  - exists 0, 0. repeat split; lia.
  - destruct IH as (q&r&(E&H&U)).
    destruct (Nat.eq_dec r d).
    + exists (S q), 0.
      assume_first.
      split; try lia. intros ????.
      assume_first. all: nia.
    + exists q, (S r).
      assume_first.
      split; try lia. intros ????.
      assume_first. all: nia.
Defined.


(* Div d x gives the number of times [d] can be substracted from [x] *)
Definition Div d x := projT1 (Euclid d x).
(* Mod d x gives the remainder of [x] after division by [d] *)
Definition Mod d x := projT1 (projT2 (Euclid d x)).


Fact Factor d x : x = (Div d x)*d + Mod d x.
Proof.
  apply (projT2 (projT2 (Euclid _ _))).
Qed.

Fact Mod_bound d x : 0 < d -> Mod d x < d.
Proof.
  apply (projT2 (projT2 (Euclid _ _))).
Qed.

Fact Factor_uniqueness d x :
  uniqueness d x (Div d x) (Mod d x).
Proof.
  apply (projT2 (projT2 (Euclid _ _))).
Qed.

Fact Mod_lt y x : 0 < y <= x -> Mod y x < x.
Proof.
  intros [H ].
  apply (Mod_bound _ x) in H. lia.
Qed.


Lemma Div_lt y x : 0 < y <= x -> 0 < Div y x.
Proof.
  intros [H1 H2].
  rewrite (Factor y x) in H2 at 1.
  apply (Mod_bound _ x) in H1.
  enough (Div y x <> 0) by lia.
  intros E. rewrite E in *; cbn in *.
  lia.
Qed.

Section Uniquness.

  Variable d : nat.

  Theorem unique x q r : r < d ->
    x = q*d + r <-> q = Div d x /\ r = Mod d x.
  Proof.
    split.
    - now apply Factor_uniqueness.
    - intros [-> ->]. apply Factor.
  Qed.

  Corollary Fac_eq q r : 
    r < d -> q = Div d (q*d + r) /\ r = Mod d (q*d + r).
  Proof. 
    intros. now apply unique.
  Qed.

  Corollary Fac_unique q1 r1 q2 r2 :
    r1 < d -> r2 < d -> q1*d + r1 = q2*d + r2 -> 
    q1 = q2 /\ r1 = r2.
  Proof.
    intros ?? H%unique.
    destruct H as [-> ->].
    apply Fac_eq.
    all: auto.
  Qed.

End Uniquness.
End Euclid.

Module Euclid2.
Definition uniqueness d x q r := 
  forall q' r', r' < d -> x = q'*d + r' -> q' = q /\ r' = r.   

Tactic Notation "assume_first" :=
  match goal with
  | H : _ |- ?A /\ ?B => 
    refine (
      (fun f a => conj a (f a)) (fun _ => _) _
    )
  end.

Definition Euclid d x :
  Sigma q r,
      x = q*d + r
  /\ (0 < d <-> r < d)
  /\ uniqueness d x q r.
Proof.
  destruct d as [|d].
  exists 0, x. repeat split; try lia.
  induction x as [|x IH].
  - exists 0, 0. repeat split; try lia.
  - destruct IH as (q&r&(E & H & U)).
    destruct (Nat.eq_dec r d).
    + exists (S q), 0.
      assume_first.
      split; try lia. intros ????.
      destruct r'.
      * nia.
      * assert (x = q' * S d + r') as H2 by lia.
        clear H1. exfalso.
        assert (r' < S d) by lia.
        specialize (U _ _ H1 H2).
        destruct U as [_ ->].
        rewrite e in H0.
        nia.
      * nia.
    + exists q, (S r).
      assume_first.
      split; try lia. intros ????.
      assume_first. all: nia.
Defined.

Definition Div d x := projT1 (Euclid d x).
Definition Mod d x := projT1 (projT2 (Euclid d x)).

Fact Factor d x : x = (Div d x)*d + Mod d x.
Proof.
  apply (projT2 (projT2 (Euclid _ _))).
Qed.

Fact Mod_bound d x : 0 < d -> Mod d x < d.
Proof.
  apply (projT2 (projT2 (Euclid _ _))).
Qed.

Fact Factor_uniqueness d x :
  uniqueness d x (Div d x) (Mod d x).
Proof.
  apply (projT2 (projT2 (Euclid _ _))).
Qed.

Fact Mod_lt y x : 0 < y <= x -> Mod y x < x.
Proof.
  intros [H ].
  apply (Mod_bound _ x) in H. lia.
Qed.


Lemma Div_lt y x : 0 < y <= x -> 0 < Div y x.
Proof.
  intros [H1 H2].
  rewrite (Factor y x) in H2 at 1.
  apply (Mod_bound _ x) in H1.
  enough (Div y x <> 0) by lia.
  intros E. rewrite E in *; cbn in *.
  lia.
Qed.

Section Uniquness.

  Variable d : nat.

  Theorem unique x q r : r < d ->
    x = q*d + r <-> q = Div d x /\ r = Mod d x.
  Proof.
    split.
    - now apply Factor_uniqueness.
    - intros [-> ->]. apply Factor.
  Qed.

  Corollary Fac_eq q r : r < d ->
      q = Div d (q*d + r) /\ r = Mod d (q*d + r).
  Proof. 
    intros. now apply unique. 
  Qed.

  Corollary Fac_unique q1 r1 q2 r2 :
    r1 < d -> r2 < d -> q1*d + r1 = q2*d + r2 -> 
    q1 = q2 /\ r1 = r2.
  Proof.
    intros ?? H%unique.
    destruct H as [-> ->].
    apply Fac_eq.
    all: auto.
  Qed.

End Uniquness.
End Euclid2.