Require Import Arith Lia.


Definition iffT (X Y : Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).


Definition dec (P : Prop) := {P} + {~P}.
Definition Dec {X} p := forall x : X, dec(p x).

Lemma dec_transport {X} p q :
  Dec p -> (forall x : X, p x <-> q x) -> Dec q.
Proof.
  intros Dec_p Equiv x.
  destruct (Dec_p x) as [H|H];
  [left | right]; firstorder.
Qed.


Lemma lt_rect f :
  (forall x, (forall y, y < x -> f y) -> f x) -> forall x, f x.
Proof.
  intros H x. apply H.
  induction x.
  - intros y. now intros F % PeanoNat.Nat.nlt_0_r. 
  - intros y Hy. apply H.
    intros z Hz. apply IHx. lia.
Defined.



(* Division with Rest *)


Definition Euclid y x :
  { a & { b &  x = a*y + b  /\  (0 < y -> b < y)  }}.
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
Definition Div y x := projT1 (Euclid y x).
(* Mod y x gives the remainder of x after division by y *)
Definition Mod y x := projT1 (projT2 (Euclid y x)).


Fact Factor y x : x = (Div y x)*y + Mod y x.
Proof.
  apply (projT2 (projT2 (Euclid _ _))).
Qed.


Fact Mod_bound y x : 0 < y -> Mod y x < y.
Proof.
  apply (projT2 (projT2 (Euclid _ _))).
Qed.

Fact Mod_lt y x : 0 < y <= x -> Mod y x < x.
Proof.
  intros [H ].
  apply (Mod_bound _ x) in H. lia.
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



Lemma Mod_divides y x : Mod y x = 0 <=> { k & x = k*y }.
Proof.
  split.
  - intros H. exists (Div y x). rewrite plus_n_O. rewrite <- H. apply Factor.
  - intros [k ->]. destruct y. cbn. lia.
    assert (0 < S y) as [? H]%(Fac_eq _ k) by lia. now rewrite <- plus_n_O in H.
Defined.

Lemma Mod_le x N : N > 0 -> Mod x N = 0 -> x <= N.
Proof.
  intros ? [[] ?]%Mod_divides; lia.
Qed.

Lemma Mod1_is_0 x : Mod 1 x = 0.
Proof.
  assert (Mod 1 x = 0 <-> Mod 1 x < 1) as -> by lia.
  apply Mod_bound; lia.
Qed.



Section Homomorphism.

  Variable m : nat.
  Local Notation "'M' x" := (Mod m x) (at level 10).
  Local Notation "'D' x" := (Div m x) (at level 10).
  

  Lemma Mod_plus_multiple d r : 
    M (d*m + r) = M r.
  Proof.
    assert (m = 0 \/ 0 < m) as [->|] by lia; cbn. lia.
    eapply (Fac_unique m _ _ (d + D r)).
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

  Fact Modm_is_0 : M m = 0.
  Proof. apply Mod_divides. exists 1. lia. Qed.

  Corollary ModMod_is_Mod x : M (M x) = M x.
  Proof.
    change (M x) with (0 + M x) at 1. 
    now rewrite <-Mod0_is_0, <-Mod_add_hom.
  Qed.


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
Qed.


Hint Resolve neg_and neg_imp eq_dec dec_conj dec_disj dec_imp dec_neg : decs.



Lemma dec_bounded_exist N p : Dec p -> dec (exists x, x < N /\ p x).
Proof.
Admitted.


Lemma dec_bounded_forall N p  : Dec p -> dec (forall x, x < N -> p x).
Proof.
Admitted.


Lemma neg_bounded_forall N p : Dec p -> (~ forall x, x < N -> p x) -> exists x, x < N /\ ~ p x. 
Proof.
  intros Hp H.
  induction N. exfalso. apply H; lia.
  destruct (Hp N).
  - destruct IHN as [n ]. 
    + intros H1. apply H. intros.
      assert (x = N \/ x < N) as [->|] by lia. 
      auto. now apply H1.
    + exists n. intuition lia. 
  - exists N. auto.
Qed.





Section PrimeDec.


  Definition irred' p := p > 1 /\ forall n, Mod n p = 0 -> (n = 1) \/ (n = p).

  Lemma irred_bounded p : (p > 1 /\ forall n, n < p -> Mod n p = 0 -> (n = 1) \/ (n = p) ) <-> irred' p.
  Proof.
    split.
    - intros [? H]. split. assumption.
      intros. enough (n < p \/ n = p) as [ | ->].
      apply H. all : auto.
      enough (n <= p) by lia.
      apply Mod_le; lia.
    - unfold irred'. intuition.
  Qed.


  Definition irred p := p > 1 /\ forall n, n < p -> Mod n p = 0 -> n = 1.

  Goal forall p, irred p <-> irred' p.
  Proof.
    unfold irred, irred'.
    setoid_rewrite <-irred_bounded.
    intuition. destruct (H1 _ H H2).
    auto. lia.
  Qed.

  Lemma dec_irred : Dec(irred).
  Proof.
    intros n. apply dec_conj. apply lt_dec.
    apply dec_bounded_forall.
    intros x. eauto with decs.
  Qed.


  Lemma irred1 N : irred N +
    (N > 1 -> {x & x < N /\ Mod x N = 0 /\ x <> 1}).
  Proof.
    destruct (dec_irred N) as [|H]; auto.
    right. intros HN. apply Witness. 
    intros x. apply dec_conj; eauto with decs. apply lt_dec.
    unfold irred in *.
    apply neg_and in H.
    - destruct H. tauto.
      apply neg_bounded_forall in H.
      destruct H as [n []].
      exists n. split. tauto.
      eauto with decs. intros x. 
      eauto with decs.
    - apply lt_dec.
    - apply dec_bounded_forall.
      intros n. apply dec_imp; eauto with decs.
  Qed.

  Lemma dec_irred_factor N : irred N + 
    (N > 1 -> {x & {y & 1 < x < N  /\ x*y = N }} ).
  Proof.
    destruct (irred1 N) as [| H]; auto.
    right. intros [x Hx]%H.
    destruct Hx as (?&[y Hy]%Mod_divides&?).
    exists x, y. nia.
  Qed.

  Lemma irred_factor n : n > 1 -> { k | irred k /\ Mod k n = 0}.
  Proof.
    induction n as [N IH] using lt_rect. intros HN.
    destruct (dec_irred_factor N) as [|H].
    - exists N. split. auto.
      apply Mod_divides. exists 1; lia.
    - destruct (H HN) as [x [y ((H1&H2)&H3) ]].
      assert (x > 1) by nia.
      destruct (IH x H2 H1) as [k Hk].
      exists k. split. tauto.
      rewrite <-H3. rewrite Mod_mult_hom, (proj2 Hk).
      apply Mod0_is_0.
  Qed.


  Lemma irred_Mod_eq m x : 
    m > 1 -> irred x -> Mod m x = 0 -> m = x.
  Proof.
    intros ? [? Hx] Eq.
    enough (m = x \/ m < x) as []; try lia.
    apply Hx in Eq; lia.
    apply Mod_le in Eq; lia.
  Qed.

  
  Lemma Nemo n a b :
    irred n -> a < n -> b < n -> n = a * b -> False.
  Proof.
    intros irred_n ? H ->.
    apply irred_n in H. lia.
    apply Mod_divides. exists a; reflexivity.
  Qed.


  Lemma Nemo' n a b :
    irred n -> 0 < a < n -> 0 < b < n -> Mod n (a * b) = 0 -> False.
  Proof.
    intros irred_n [? Ha] [? Hb] [k Hk]%Mod_divides.
    apply irred_n in Ha. rewrite Ha in *.
    all: assert (k = 0 \/ k = 1 \/ k > 1) as [ ->|[->|]] by lia; try nia.
    exfalso. apply (Nemo n a b); auto; lia.
  Admitted.


  Lemma irred_integral_domain' n a b : irred n ->
    Mod n a <> 0 -> Mod n b <> 0 -> Mod n (a * b) <> 0 .
  Proof.
    intros irred_n Ha Hb Eq.
    rewrite <-ModMod_is_Mod in Ha, Hb.
    rewrite Mod_mult_hom in Eq.
    apply (Nemo n (Mod n a) (Mod n b)).
    apply irred_n.
    all: try (destruct irred_n; apply Mod_bound; lia).
    apply Mod_le in Eq.
  Admitted.


  Lemma irred_integral_domain n a b : irred n ->
    Mod n (a * b) = 0 -> Mod n a = 0 \/ Mod n b = 0.
  Proof.
  Admitted.


  Lemma irred_inverses n a : irred n ->
    Mod n a <> 0 -> exists b, Mod n (a * b) = 1.
  Proof.
  Admitted.



  Definition prime p := p > 1 /\ forall a b, Mod p (a * b) = 0 -> Mod p a = 0 \/ Mod p b = 0.

  Lemma prime_irred_equiv p : irred p <-> prime p.
  Proof.
    split; intros [? H]; split; auto.
    - intros a b. now apply irred_integral_domain.
    - intros n H1 H2. 
      destruct (fst (Mod_divides _ _) H2) as [k Hk].
      destruct (H k n).
      + rewrite <-Hk. apply Mod_divides. exists 1. now cbn.
      + destruct (fst (Mod_divides _ _) H3) as [? ->].
        assert (p*(x*n) = p*1) as ?%Nat.mul_cancel_l by lia.
        apply Nat.mul_eq_1 in H5. all: lia.
      + apply Mod_le in H3. all: lia.
  Qed.

  Corollary dec_prime : Dec(prime).
  Proof.
    refine (dec_transport _ _ dec_irred prime_irred_equiv).
  Qed.


End PrimeDec.




Section PrimeInf.


  Fixpoint faktorial n :=
    match n with
    | 0 => 1
    | S x => (faktorial x)*n
    end.

  Notation "x !" := (faktorial x) (at level 2).


  Fact fac1 : forall n, 0 < n!.
  Proof. induction n; cbn; lia. Qed.

  Fact fac2 : forall n, 0 < n -> Mod n (n !) = 0.
  Proof.
    intros n H. destruct n; try lia.
    apply Mod_divides. exists (n !). 
    reflexivity.
  Qed.

  Lemma fac3 : forall x y, 0 < y <= x -> Mod y (x!) = 0.
  Proof.
    intros x y H.
    induction x in y, H |-*.
    - lia.
    - assert (y = S x \/ y <= x) as [<-|] by lia; cbn.
      now apply fac2.
      rewrite Mod_mult_hom, IHx.
      apply Mod0_is_0. lia.
  Qed.



  Goal forall N, exists p, N < p /\ irred p.
  Proof.
    intros n.
    destruct (irred_factor (n! + 1)) as [k [[] ]].
    specialize(fac1 n). lia.
    exists k. split.
    - rewrite Mod_add_hom in *.
      assert (n < k <-> ~ (k <= n)) as G by lia.
      apply G. intros ?.
      enough (1 = 0) by lia.
      rewrite <-H1 at 2.
      rewrite fac3. 2: lia. 
      cbn; rewrite ModMod_is_Mod.
      symmetry. refine ( proj2 (Fac_eq _ 0 _ _)); lia.
    - unfold irred. tauto.
  Qed.


End PrimeInf.




Section PrimeDecomp.


  Lemma exponent p X : Mod p X = 0 ->
    { k & {x & X = x * p^k /\ (p > 1 -> X <> 0 -> Mod p x <> 0) }}.
  Proof.
    intros H. destruct p as [|[]].
    - cbn in *. rewrite H.
      exists 0, 0; cbn; lia.
    - exists 0, X; cbn; lia.
    - induction X as [X Hrec] using lt_rect.
      destruct X.
      exists 0, 0; cbn; split; auto.
      apply Mod_divides in H.
      destruct H as [x Hx].
      destruct (eq_dec (Mod (S (S n)) x) 0 ).
      + destruct (Hrec x) as (k' & x' & H'); try lia. 
        exists (S k'), x'.
        split; rewrite Hx, (proj1 H'). cbn; lia.
        intros. apply H'; lia. 
      + exists 1, x; cbn; intuition lia.
  Defined.


  Definition expo p X := 
    match (eq_dec (Mod p X) 0) with
    | left H => (projT1 (exponent p X H))
    | right _ => 0
    end.


  Lemma expo_hom p x y : p > 1 -> 
    expo p (x * y) = expo p x + expo p y.
  Proof.
    intros Hp.
    destruct x.
    
  Admitted.


  Lemma prime_decomp x y :
    (forall p, prime p -> expo p x = expo p y) -> x = y.
  Proof.
    revert y. pattern x. revert x. apply lt_rect.
    intros x Hrec. intros y H.
  Admitted.


End PrimeDecomp.