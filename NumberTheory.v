Require Import Arith Lia.


Definition iffT (X Y : Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).


Definition dec (P : Prop) := {P} + {~P}.
Definition Dec {X} p := forall x : X, dec(p x).

Lemma dec_transport {X} p q :
  Dec p -> (forall x : X, p x <-> q x) -> Dec q.
Proof.
  intros Dec_p Equiv x.
  destruct (Dec_p x) as [H|H].
  - left. firstorder.
  - right. firstorder.
Qed.



(* Division with Rest *)


Definition DIV y x :
  { a & { b &   x = a*y + b  /\  (0 < y -> b < y)  }}.
Proof.
  destruct y as [|y].
  exists 0, x. repeat split; lia.
  induction x as [|x IH].
  - exists 0, 0. repeat split; lia.
  - destruct IH as (a&b&[]).
    destruct (Nat.eq_dec b y).
    + exists (S a), 0. split; lia.
    + exists a, (S b). split; lia.
Defined.


(* Div y x gives the number of times y can be substracted from x *)
Definition Div y x := projT1 (DIV y x).
(* Mod y x gives the remainder of x after division by y *)
Definition Mod y x := projT1 (projT2 (DIV y x)).


Fact Factor y x : x = (Div y x)*y + Mod y x.
Proof.
  apply (projT2 (projT2 (DIV _ _))).
Qed.


Fact Mod_bound y x : 0 < y -> Mod y x < y.
Proof.
  apply (projT2 (projT2 (DIV _ _))).
Qed.



Section Uniquness.

  Variable y : nat.
  
  (* Lemma both_are_O a b : *)
  (*   a*y = b -> b < y -> a = 0 /\ b = 0. *)
  (* Proof. *)
  (*   intros E. assert (y = 1*y) as -> by lia. *)
  (*   rewrite <-E. intros ?%Nat.mul_lt_mono_pos_r. *)
  (*   split. all: nia. *)
  (* Qed. *)


  Lemma Fac_unique a1 b1 a2 b2 : b1 < y -> b2 < y ->
            a1*y + b1 = a2*y + b2 -> a1 = a2 /\ b1 = b2.
  Proof.
    intros. destruct (le_ge_dec a1 a2).
    1 : cut (a2 * y - a1 * y = b1 - b2).
    3 : cut (a1 * y - a2 * y = b2 - b1).
    all : try (rewrite <- Nat.mul_sub_distr_r); nia.
  Qed.


  Theorem unique x a b : b < y ->
    x = a*y + b <-> a = Div y x /\ b = Mod y x.
  Proof.
    split.
    - rewrite (Factor y x) at 1. intros.
      specialize (Mod_bound y x) as ?.
      apply Fac_unique; lia.
    - intros [-> ->]. apply Factor.
  Qed.
  
  
  Corollary Fac_eq a b : b < y ->
      a = Div y (a*y + b) /\ b = Mod y (a*y + b).
  Proof. intros. now apply (unique _). Qed.  


End Uniquness.


Lemma Mod_for_multiple y x : Mod y x = 0 <=> { k & x = k*y }.
Proof.
  split.
  - intros H. exists (Div y x). rewrite plus_n_O. rewrite <- H. apply Factor.
  - intros [k ->]. destruct y. cbn. lia.
    assert (0 < S y) as [? H]%(Fac_eq _ k) by lia. now rewrite <- plus_n_O in H.
Qed.




Section WitnessOperator.

  Variable q : nat -> Prop.
  Variable Dec_q : Dec q.

  Inductive T n : Prop :=
    C : (~ q n -> T (S n)) -> T n.


  Lemma grounded n : T n -> T 0.
  Proof.
    induction n; auto.
    intros. apply IHn. now constructor.
  Defined.

  Lemma qT n : q n -> T n.
  Proof.
    intros. now constructor.
  Defined.

  Lemma preWitness : forall n, T n -> {x & q x}.
  Proof.
    apply T_rect.
    intros n _ H. destruct (Dec_q n).
    now exists n. now apply H.
  Defined.

  Theorem Witness : (exists x, q x) -> {x & q x}.
  Proof.
    intros H. apply (preWitness 0).
    destruct H as [n H]. destruct (Dec_q n).
    - eapply grounded, qT, H.
    - tauto.
  Defined.

End WitnessOperator.


Lemma dec_bounded_exist N p : dec (exists x, x < N /\ p x).
Proof.
Admitted.


Lemma dec_conj A B : dec A -> dec B -> dec (A /\ B).
Proof.
  intros [] []; unfold dec; now (left + right).
Defined.

Lemma dec_neg A : dec A -> dec (~ A).
Proof.
  intros []; unfold dec; now (left + right).
Defined.

Lemma DeMorgan A B : dec A -> dec B -> ~(A /\ B) -> (~A \/ ~B).
Proof.
  intros [] [] ?; tauto.
Defined.



(* Decider for prime numbers *)


Definition divides n m := exists k, m = k*n.

Definition prime p := p > 1 /\ forall n, divides n p -> (n = 1) \/ (n = p).


Lemma divides_le x N : N > 0 -> divides x N -> x <= N.
Proof.
  intros ? [k ?]. assert (k > 0) by lia. nia.
Qed.



Lemma dec_divides x n : dec(divides x n).
Proof.
  unfold divides.
  destruct (Nat.eq_dec (Mod x n) 0 ) as [ [k H]%Mod_for_multiple |H].
  - left. exists k; auto.
  - right. intros [k Hk]. apply H, Mod_for_multiple.
    exists k; auto.
Qed.


Definition Q N x := x <> 1 /\ divides x N.


Lemma Dec_Q : forall N, Dec(Q N).
Proof.
  intros N x. apply dec_conj.
  apply dec_neg. unfold dec. decide equality. 
  apply dec_divides.
Qed.


Lemma dec_bounded_Q N : 
  { x & x < N /\ Q N x } + forall x, x < N -> ~ Q N x.
Proof.
  destruct (dec_bounded_exist N (Q N)).
  - left. apply Witness. 2 : assumption.
    intros x. apply dec_conj. apply lt_dec. apply Dec_Q.
  - right. firstorder.
Qed.


Lemma negQ_prime N : N > 1 ->
  (forall x, x < N -> ~ Q N x) -> prime N.
Proof.
  intros HN H. split. auto. unfold Q in *.
  intros x. specialize (H x).
  intros DxN.
  assert (N > 0) as N0 by lia.
  specialize (divides_le _ _ N0 DxN) as ?.
  assert (x = N \/ x < N) as [|F] by lia; auto.
  specialize (H F). apply DeMorgan in H. intuition lia.
  apply dec_neg. unfold dec. decide equality. 
  apply dec_divides.
Qed.


Lemma dec_prime' N : N > 1 -> 
  {x & x < N /\ x <> 1 /\ divides x N } + prime N.
Proof.
  intros H. destruct (dec_bounded_Q N).
  - now left.
  - right. now apply negQ_prime.  
Defined.


Lemma dec_prime {N} : N > 1 -> 
  {x & {y & x < N /\ y < N /\ x*y = N }} + prime N.
Proof.
  intros HN.
  destruct (dec_prime' N HN) as [ [x (?&?&div)]  |].
  - left. apply Witness in div. destruct div as [y Hy].
    exists x, y. nia. 
    intros ?. unfold dec. decide equality.
  - now right.
Qed.



Definition primeb N :=
match (lt_dec 1 N) with
| left H => if (dec_prime H) then false else true
| right _ => false
end.


Definition decomp' N := 
match (lt_dec 1 N) with
| left H => match (dec_prime H) with 
            | inl Div  => projT1 Div
            | inr _ => N
            end
| right _ => N
end.







Fixpoint pow k x := 
  match k with
  | 0 => 1
  | S n => x*(pow n x)
  end.

Notation "x ^^ k" := (pow k x) (at level 19).


Lemma lt_rect f : 
(forall x, (forall y, y < x -> f y) -> f x) -> forall x, f x.
Proof.
Admitted.

Lemma exponent x p : p > 1 ->
  { k & Mod ( p^^k ) (S x) = 0 /\ Mod ( p^^(S k) ) (S x) <> 0 }.
Proof.
  intros Hp.
  destruct x.
  - exists 0. cbn. repeat split. intros []%Mod_for_multiple.
    destruct x; lia.
  - revert x. apply lt_rect. intros x rect.
    remember (S (S x)) as N. assert (N > 1) by lia.
Admitted.

Definition expo x p := 
  match (lt_dec 1 p) with
  | left H => Some (projT1 (exponent x p H))
  | right _ => None
  end.

Lemma prime_decomp x y :
  (forall p, prime p -> expo x p = expo y p) -> x = y.
Proof.
Admitted.






