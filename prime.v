Require Import Arith Lia.


Definition iffT (X Y : Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).


Definition dec (P : Prop) := {P} + {~P}.
Definition Dec {X} p := forall x : X, dec(p x).




(* Division with Rest *)


Definition Euclid y x :
  { a & { b &  x = a*y + b  /\  (0 < y <-> b < y)  }}.
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


Definition Div y x := projT1 (Euclid y x).
Definition Mod y x := projT1 (projT2 (Euclid y x)).


Fact Factor y x : x = (Div y x)*y + Mod y x.
Proof.
  apply (projT2 (projT2 (Euclid _ _))).
Qed.

Fact Mod_bound y x : 0 < y -> Mod y x < y.
Proof.
  apply (projT2 (projT2 (Euclid _ _))).
Qed.



Section Uniquness.

  Variable m : nat.
  
  Lemma Fac_unique a1 b1 a2 b2 : b1 < m -> b2 < m ->
    a1*m + b1 = a2*m + b2 -> a1 = a2 /\ b1 = b2.
  Proof.
    intros.
    destruct (Nat.lt_trichotomy a1 a2) as [ |[]]; nia.
  Qed.


  Theorem unique x a b : b < m ->
    x = a*m + b <-> Div m x = a /\ Mod m x = b.
  Proof.
    split.
    - rewrite (Factor m x) at 1. intros.
      specialize (Mod_bound m x) as ?.
      apply Fac_unique; lia.
    - intros [<- <-]. apply Factor.
  Qed.
  
  
  Corollary Fac_eq a b : b < m ->
      Div m (a*m + b) = a /\ Mod m (a*m + b) = b.
  Proof. intros. now apply (unique _). Qed.


End Uniquness.



Notation "x '<d' y" := ( exists k, x*k = y ) (at level 30).

Lemma Mod_divides y x : Mod y x = 0 <=> { k & x = k*y }.
Proof.
  split.
  - intros H. exists (Div y x). rewrite plus_n_O. rewrite <- H. apply Factor.
  - intros [k ->]. destruct y. 
    + cbn. lia.
    + assert (0 < S y) as [? H]%(Fac_eq _ k) by lia. 
      now rewrite <- plus_n_O in H.
Defined.



Section Homomorphism.

  Variable m : nat.
  Local Notation "'M' x" := (Mod m x) (at level 10).
  Local Notation "'D' x" := (Div m x) (at level 10).
  

  Lemma Mod_plus_multiple d r : 
    M (d*m + r) = M r.
  Proof.
    assert (m = 0 \/ 0 < m) as [->|] by lia; cbn. 
    - lia.
    - eapply (Fac_unique m _ _ (d + D r)).
      all: try now apply Mod_bound.
      rewrite <-Factor.
      rewrite (Factor m r) at 1. lia.
  Qed.

  
  Theorem Mod_add_hom x y: 
    M (x + y) = M (M x + M y).
  Proof.
    symmetry.
    rewrite <-(Mod_plus_multiple (D x + D y)).
    rewrite (Factor m x), (Factor m y) at 3.
    f_equal. lia.
  Qed.

  
  Theorem Mod_mult_hom x y:
    M (x * y) = M (M x * M y).
  Proof.
    symmetry.
    erewrite <-(Mod_plus_multiple (D x * D y * m + D x * M y + D y * M x )).
    rewrite (Factor m x), (Factor m y) at 5.
    f_equal. lia.
  Qed.

  Fact Mod0_is_0 : M 0 = 0.
  Proof. destruct m; reflexivity. Qed.



End Homomorphism.



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



Lemma lt_dec x y : dec (x < y).
Proof.
  induction y in x |-*.
  - right. lia.
  - destruct x.
    + left. lia.
    + destruct (IHy x); (left + right); lia.
Qed.

Lemma eq_dec (x y : nat) : dec (x = y).
Proof.
  unfold dec. decide equality.
Defined.

Lemma dec_conj A B : dec A -> dec B -> dec (A /\ B).
Proof.
  intros [] []; unfold dec; intuition.
Defined.

Lemma dec_disj A B : dec A -> dec B -> dec (A \/ B).
Proof.
  intros [] []; unfold dec; intuition.
Defined.


Lemma dec_imp A B : dec A -> dec B -> dec (A -> B).
Proof.
  intros [] []; unfold dec; intuition.
Defined.

Lemma dec_neg A : dec A -> dec (~ A).
Proof.
  intros []; unfold dec; now (left + right).
Defined.

Lemma neg_and A B : dec A -> dec B -> ~(A /\ B) -> (~A \/ ~B).
Proof.
  intros [] [] ?; tauto.
Defined.

Lemma neg_imp A B : dec A -> dec B -> ~(A -> B) -> A /\ ~B.
Proof.
  intros [][]?; tauto.
Defined.


Hint Resolve neg_and neg_imp eq_dec dec_conj dec_disj dec_imp dec_neg : decs.


Lemma dec_lt_bounded N p : 
  Dec p -> (forall x, x < N -> p x) + { x & x < N /\ ~ p x}.
Proof.
  intros Dec_p. induction N.
  - left. lia.
  - specialize (IHN) as [IH | IH].
  + destruct (Dec_p N) as [HN | HN].
    * left. intros x Hx.
      assert (x = N \/ x < N) as [->|] by lia; auto.
    * right. exists N. split; auto.
  + right. destruct IH as [x Hx].
    exists x. split.
    * lia.
    * apply Hx.
Defined.


Lemma dec_lt_bounded_forall N p :
  Dec p -> dec (forall x, x < N -> p x).
Proof.
  intros Dec_p.
  destruct (dec_lt_bounded N _ Dec_p) as [|[x Hx]].
  - now left.
  - right. intros H. now apply Hx, H.
Defined.


Lemma neg_lt_bounded_forall N p :
  Dec p -> (~ forall x, x < N -> p x) -> exists x, x < N /\ ~ p x.
Proof.
  intros Dec_p H.
  destruct (dec_lt_bounded N _ Dec_p) as [|[x Hx]].
  - tauto.
  - now exists x. 
Qed.





Section PrimeDec.


  Definition prime p := p > 1 /\ forall n, n < p -> Mod n p = 0 -> n = 1.

  Lemma dec_prime : Dec(prime).
  Proof.
    intros n. apply dec_conj. 
    - apply lt_dec.
    - apply dec_lt_bounded_forall.
      intros x. eauto with decs.
  Defined.

  Lemma prime_or_div' N : 
    prime N + (N > 1 -> {x & x < N /\ Mod x N = 0 /\ x <> 1}).
  Proof.
    destruct (dec_prime N) as [|H]; auto.
    right. intros HN. apply Witness. 
    - intros x. apply dec_conj; eauto with decs. apply lt_dec.
    - unfold prime in *.
      apply neg_and in H.
    --  destruct H. 
        + tauto.
        + apply neg_lt_bounded_forall in H.
        ++  destruct H as [n []].
            exists n. split; auto.
            eauto with decs. 
        ++  intros x. eauto with decs.
    --  apply lt_dec.
    --  apply dec_lt_bounded_forall.
        intros n. apply dec_imp; eauto with decs.
  Defined.

  Lemma prime_or_div N :
    prime N + (N > 1 -> {q & 1 < q < N /\ q <d N} ).
  Proof.
    destruct (prime_or_div' N) as [| H]; auto.
    right. intros [x Hx]%H.
    destruct Hx as (?&[y ->]%Mod_divides&?).
    exists x. repeat split. 
    - lia.
    - lia.
    - exists y. lia.
  Defined.




  Lemma lt_rect f :
    (forall x, (forall y, y < x -> f y) -> f x) -> forall x, f x.
  Proof.
    intros H x. apply H.
    induction x.
    - intros y. lia.
    - intros y Hy. apply H.
      intros z Hz. apply IHx. lia.
  Defined.

  Lemma prime_factor n : 
    n > 1 -> { q | prime q /\ q <d n}.
  Proof.
    induction n as [N IH] using lt_rect. intros HN.
    destruct (prime_or_div N) as [|H].
    - exists N. split. 
      + auto.
      + exists 1; lia.
    - destruct (H HN) as [q ((H1&H2)&H3)] .
      (* assert (q > 1) by lia. *)
      destruct (IH q H2 H1) as [k Hk].
      exists k. split. 
      + tauto.
      + destruct H3 as [a <-], Hk as [? [b <-]].
        exists (b * a). lia.
  Qed.


End PrimeDec.