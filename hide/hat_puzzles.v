Require Import Lia.

Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

(* 

Alice and Bob are wearing hats. On each hat either "true" or "false" is written. Both can see each other’s hats, but not their own hat. They are tasked with guessing their own hat color. If either person gets the color right, they win. 
They cannot communicate with each other in any way after the hats have been placed on their heads and they must both say their guess at exactly the same time. However, they can meet in advance to decide on a strategy. Find a strategy that guarantees a payoff.

*)

Implicit Type hat_A hat_B : bool.

(* The strategy is that one of the players guesses that they both have the same value on their hats, and the second one guesses that he has a different value on his hat. *)
Lemma puzzle1 :
  Sigma Alice_guess Bob_guess, forall hat_A hat_B,
    {Alice_guess hat_B = hat_A} + {Bob_guess hat_A = hat_B}.
Proof.
  exists (fun x => x), negb.
  (* With the chosen strategies we now just need to prove that equality on booleans is decidable *)
  intros [] []; auto.
Qed.


Section Choice.

Definition AC :=
  forall X Y (p : X -> Y -> Prop),
  (forall x, exists y, p x y) -> (Sigma f, forall x, p x (f x)).

Hypothesis ac : AC.


Definition eq {X} (f g : nat -> X) :=
  exists s1 s2, forall n, f (s1 + n) = g (s2 + n).


Fact eq_refl {X} f : @eq X f f.
Proof.
  exists 0, 0. reflexivity.
Qed.

Fact eq_symm {X} f g : @eq X f g -> eq g f.
Proof.
  intros (s1 & s2 & H).
  exists s2, s1. intros ?. symmetry.
  now apply H.
Qed. 

Lemma eq_trans {X} f g h :
  @eq X f g -> eq g h -> eq f h.
Proof.
  intros (s1 & s2 & H) (s2' & s3 & H').
  destruct (PeanoNat.Nat.lt_trichotomy s2 s2') as [|[->|]].
  - exists (s1 + (s2' - s2)), s3. intros ?.
    replace (s1 + (s2' - s2) + n) with (s1 + (s2' - s2 + n)) by lia.
    rewrite H, <-H'; f_equal; lia.
  - exists s1, s3. intros ?.
    rewrite H, <-H'; reflexivity.
  - exists s1, (s3 + (s2 - s2')). intros ?.
    replace (s3 + (s2 - s2') + n) with (s3 + (s2 - s2' + n)) by lia.
    rewrite H, <-H'; f_equal; lia.
Qed.


Definition cut {X} n (f : nat -> X) := fun x => f (n + x). 

Lemma eq_cut {X} n f : @eq X f (cut n f).
Proof.
  exists n, 0. intros ?.
  unfold cut. f_equal.
Qed.


Definition eq' {X} (f g : nat -> X) :=
  exists B, forall n, n >= B -> f n = g n.




Implicit Type f : nat -> bool.


Fact C_ : Sigma C, forall f, (forall g, eq' g f -> eq' g (C f)).
Proof.
  apply ac with (p := fun x y => forall g, eq' g x -> eq' g y). 
  intros f. exists f. tauto.
Defined.

Definition C := projT1 C_.
Definition C_spec := projT2 C_.

Lemma C_func f g : eq' f g -> C f = C g.
Proof.
Admitted.


Lemma puzzle2 :
  forall F : nat -> bool,
    exists Guess n, forall p, p >= n ->
      F p = Guess (cut (S p) F) p.
Proof.
  intros F.
  specialize (C_spec (C F) F) as (B & H). 
  - apply C_spec. now exists 0. 
  - exists C, B. intros p Hp.
    rewrite H; auto.
    erewrite C_func. 1: reflexivity.
    
Admitted.

End Choice.
