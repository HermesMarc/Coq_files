Require Import Equations.Equations.
Require Import Arith Lia.


(** Formalized Solution for the following riddle *)

(* You’re facing your friend, Caryn, in a “candy-off,” which works as follows: There’s a pile of 100 caramels and one peppermint patty. 
You and Caryn will go back and forth taking at least one and no more than five caramels from the candy pile in each turn. The person 
who removes the last caramel will also get the peppermint patty. And you love peppermint patties.

Suppose Caryn lets you decide who goes first. Who should you choose in order to make sure you win the peppermint patty?

*)


(*** Preliminaries *)
(*We need some facts about division with remainder *)

Definition iffT (X Y : Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).


Definition DIV y x :
  sigT(fun a => sigT (fun b => x = a * y + b /\ (0 < y -> b < y)  )).
Proof.
  destruct y as [|y].
  exists 0, x. repeat split. lia.
  induction x as [|x IH].
  - exists 0, 0. repeat split. tauto.
  - destruct IH as (a&b&H).
    destruct (Nat.eq_dec b y).
    + exists (S a), 0. repeat split; lia.
    + exists a, (S b). repeat split; lia.
Defined.


(* D y x gives the number of times y can be substracted from x *)
Definition D y x := projT1 (DIV y x).
(* M y x gives the remainder of x after division by y *)
Definition M y x := projT1 (projT2 (DIV y x)).


Fact Factor y x : x = (D y x)*y + M y x.
Proof.
  apply (projT2 (projT2 (DIV _ _))).
Qed.

Fact M_bound y x : 0 < y -> M y x < y.
Proof.
  apply (projT2 (projT2 (DIV _ _))).
Qed.


Section Uniqueness.

  Variables y : nat.

  Lemma Fac_unique a1 b1 a2 b2 : b1 < y -> b2 < y ->
    a1*y + b1 = a2*y + b2 -> a1 = a2 /\ b1 = b2.
  Proof.
    intros.
    destruct (Nat.lt_trichotomy a1 a2) as [ |[]]; nia.
  Qed.


  Theorem unique x a b : b < y ->
    x = a*y + b <-> a = D y x /\ b = M y x.
  Proof.
    split.
    - rewrite (Factor y x) at 1. intros.
      specialize (M_bound y x) as ?.
      apply Fac_unique; lia.
    - intros [-> ->]. apply Factor.
  Qed.

  
  Corollary Fac_eq a b : b < y ->
      a = D y (a*y + b) /\ b = M y (a*y + b).
  Proof.
    intros. now apply (unique _).
  Qed.  


End Uniqueness.


Lemma M_for_multiple : forall y x, M y x = 0 <=> { k & x = k*y }.
Proof.
  split.
  - intros H. exists (D y x). rewrite plus_n_O. rewrite <- H. apply Factor.
  - intros [k ->]. destruct y. cbn. lia.
    assert (0 < S y) as [? H]%(Fac_eq _ k) by lia. now rewrite <- plus_n_O in H. 
Qed.


Lemma non_div y x z : 0 < x -> M y x = 0 -> 0 < z < y -> M y (x - z) <> 0.
Proof.
  intros Hx [k ->]%M_for_multiple Hz [l Hl]%M_for_multiple. 
  apply Nat.lt_0_mul' in Hx. destruct Hx.
  enough (k * y + 0 = l * y + z) as G%Fac_unique; destruct k; lia.
Qed.
  

Lemma complete_ind (P : nat -> Type) :
  (forall x, (forall y, y < x -> P y) -> P x) -> forall x, P x.
Proof.
  intros H x. apply H.
  induction x.
  - intros y. now intros F % PeanoNat.Nat.nlt_0_r. 
  - intros y Hy. apply H.
    intros z Hz. apply IHx. lia.
Qed.





(*** Riddle Solution *)
Section Riddle.

  (* The pile has *) Variable N : nat. (* patties in it *)
  (* And there are two players *)
  Inductive player := Caryn | Me.
  (* Who must remove at least 1 and less than*) Variable t : nat. (* patties every turn. *)
  
  Definition switch p := match p with
                         | Caryn => Me
                         | Me => Caryn end.

  
  (* A player looks at how many patties there are left and removes 1,...,5 of them. So his choices can be modeled as a function with bounded output possibilities *)
  Definition choice := { f : nat -> nat | forall k, 0 < f k < 6}.
  Variable CarynChoice : choice.


  (* This calculates the winner of the game given the choices c m, the starting height N of the stack and starting player p *)
  Equations Game (N : nat) (p : player) (c m : choice) : player by wf N :=
    Game O p c m := switch p;
    Game N Caryn c m := Game (N - (proj1_sig c) N) Me c m;
    Game N Me c m := Game (N - (proj1_sig m) N) Caryn c m.
  Next Obligation.
    destruct c as [f Hf]. cbn. destruct (f (S n)) eqn:Bot.
    specialize (Hf (S n)). all : lia.
  Defined.
  Next Obligation.
    destruct m as [f Hf]. cbn. destruct (f (S n)) eqn:Bot.
    specialize (Hf (S n)). all : lia.
  Defined.
  
  
  (* This specifies my choice on every turn: I will always take a number of patties such that the height becomes divisible my 6 again. *)
  Lemma MyChoice : choice.
  Proof.
    exists (fun k => if nat_eqdec (M 6 k) O then 1 else M 6 k).
    intros k. destruct (nat_eqdec (M 6 k) O).
    - lia.
    - split. lia. apply M_bound. lia.
  Defined.


  
  Definition myChoice := proj1_sig MyChoice.

  Lemma MyChoiceSpec n : M 6 n <> 0 -> myChoice n = M 6 n.
  Proof.
    unfold myChoice. cbn. now destruct (nat_eqdec (M 6 n) O).
  Qed.


  (* This gives the winner of the game between me and Caryn *)
  Definition Winner N First := Game N First CarynChoice MyChoice.

  
  Theorem WinChoice :
    (M 6 N = 0 -> Winner N Caryn = Me) /\ (M 6 N <> 0 -> Winner N Me = Me).    
  Proof.
    pattern N. revert N. apply complete_ind. intros N IH.
    destruct (nat_eqdec (M 6 N) O) as [H|H].
    - split. 2 : tauto. intros _.
      destruct N. now simp Game.
      specialize (proj2_sig CarynChoice (S n)) as Rules.
      unfold Winner; simp Game. apply IH.
      lia. apply non_div; lia.
    - split. tauto. intros _. destruct N.
      + cbn in H. congruence.
      + unfold Winner. simp Game.
        fold myChoice. rewrite (MyChoiceSpec _ H).
        rewrite (Factor 6 (S n) ) at 1. rewrite Nat.add_sub. apply IH.
        rewrite (Factor 6 (S n) ) at 2. lia.
        rewrite (plus_n_O (_*_) ). symmetry. apply Fac_eq; lia.
  Qed.

  
  (* From the above we immediately get that it is always possible to choose the starting player so that I can win  *)
  Corollary Winable :
    exists p : player, Winner N p = Me.
  Proof.
    destruct (nat_eqdec (M 6 N) O);
    (exists Caryn + exists Me); now apply WinChoice.
  Qed.
  
  
End Riddle.