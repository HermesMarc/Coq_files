(* Expressing that X has at most two elements:
  Whenever we have three x y z, then at least one pair is identical *)
Definition most_2 X :=
  forall x y z : X, x = y \/ x = z \/ y = z.
Definition Kaminski X := forall f (x : X), f (f (f x)) = f x.
Definition Eq X := forall x y : X, {x = y} + {~ x = y}.

Goal forall X, Eq X -> Kaminski X -> most_2 X.
Proof.
  intros X eq Kam x1 x2 x3.
  pose (f := fun x =>
    if eq x x1 then x2
    else if eq x x2 then x3 else x1).
  destruct (eq x1 x3), (eq x2 x3); auto.
  left. specialize (Kam f x1). unfold f in *.
  destruct (eq x1 x1), (eq x2 x2), (eq x2 x1), (eq x3 x1), (eq x3 x2); congruence.
Qed.

Goal forall X, most_2 X -> Kaminski X.
Proof.
  intros X H f x.
  specialize (H (f(f x)) (f x) x).
  intuition congruence.
Qed.


Load Preamble.

Fixpoint Num (n : nat) : Type :=
  match n with 
  | 0 => False 
  | S n => option (Num n) 
  end.

Fixpoint iter {X} (f : X -> X) n a : X := 
  match n with
  | 0 => a
  | S m => f (iter f m a)
  end.

Definition pigeonhole n (X : Type) :=
  forall f : nat -> X, Sigma i j, i <= S n /\ j <= S n /\ i <> j /\ f i = f j.
Definition Kaminski' n X := forall f (x : X), f (iter f n x) = f x.


Goal forall n X, pigeonhole n X -> Eq X.
Proof.
  intros n X P x y.
Admitted.  

Require Import Lia.

Goal forall X n, Eq X -> Kaminski' (S n) X -> pigeonhole (S n) X.
Proof.
  intros X n eq K g.
  pose (perm f := fix p n x := 
    match n with
    | 0 => x
    | 1 => (f 0)
    | S m => if eq x (f n) then (f 0) else p m x
    end).
  induction n.
  - exists 0, 1; repeat split; try lia.
    remember (g 0) as x0.
    remember (g 1) as x1.
    pose (f x := if eq x x0 then x1 else x0).
    assert (f x1 = f x0).
    + rewrite <-(K f). cbn. unfold f.
    now destruct (eq x1 x0), (eq x1 x0), (eq x0 x0).
    + unfold f in *. 
      now destruct (eq x1 x0), (eq x0 x0).
  -  
      
  (* assert (~ forall i j : Num (S n), f i = f j -> i = j) as H.
   *)

Admitted.