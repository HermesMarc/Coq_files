Require Import Equations.Equations.
Require Import Arith Lia.


Definition Euclid q x :
  { d & { r &  x = d*q + r  /\  (0 < q <-> r < q)  }}.
Proof.
  destruct q as [|q].
  exists 0, x. repeat split; lia.
  induction x as [|x IH].
  - exists 0, 0. repeat split; lia.
  - destruct IH as (d&r&[]).
    destruct (Nat.eq_dec r q).
    + exists (S d), 0. split; lia.
    + exists d, (S r). split; lia.
Defined.

Definition Div y x := projT1 (Euclid y x).
Definition Mod y x := projT1 (projT2 (Euclid y x)).

Fact Factor y x : x = (Div y x)*y + Mod y x.
Proof. apply (projT2 (projT2 (Euclid _ _))). Qed.

Fact Mod_bound y x : 0 < y -> Mod y x < y.
Proof. apply (projT2 (projT2 (Euclid _ _))). Qed.


Equations gcd (x y : nat) : nat by wf x :=
  gcd 0 y := y;
  gcd x y := gcd (Mod x y) x.
Next Obligation.
  apply Mod_bound. lia.
Defined.


Lemma Bezout :
  forall x y, exists a b, x*a + y*b = gcd x y + x*y /\ (0 < x -> b <= x) /\ (0 < y -> a <= y). 
Proof.
  induction x as [x rec] using lt_wf_rect.
  intros y. destruct x.
  - simp gcd. exists 0, 1. lia.
  - assert (Lt : Mod (S x) y < S x ).
    + apply Mod_bound; lia.
    + simp gcd.
      destruct (rec (Mod (S x) y) Lt (S x)) as (a & b & H &?&?).
      exists (x*Div (S x) y - a), b. repeat split.
      * rewrite (Factor (S x) y) at 4. admit.
      * admit.
      *  
      