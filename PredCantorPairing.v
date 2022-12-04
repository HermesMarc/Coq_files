Require Import Arith Lia.

Definition iffT (X Y : Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).


Definition inj {X Y} (f : X -> Y) :=
  forall x x', f x = f x' -> x = x'.
  
Definition inv {X Y} (g : Y -> X) (f : X -> Y) :=
  forall x, g (f x) = x.

Definition bijection X Y :=
  { f : X -> Y & { g & inv g f /\ inv f g }}.


Lemma size_rect {X} σ f : 
  (forall x, (forall y : X, σ y < σ x -> f y) -> f x) -> forall x, f x.
Proof.
  intros H x. apply H.
  induction (σ x).
  - intros y. now intros F % PeanoNat.Nat.nlt_0_r. 
  - intros y Hy. apply H.
    intros z Hz. apply IHn. lia.
Defined.



Section Cantor.

Definition next '(x,y) := 
  match x with
  | O => (S y, O)
  | S x' => (x', S y)
  end.

Fact n00_next : forall p, (0,0) <> next p.
Proof. destruct p as [[] ]; intuition discriminate. Qed.

Fact inj_next : inj next.
Proof. intros [[] ][[] ]; cbn; congruence. Qed.



Fixpoint decode n := 
  match n with
  | 0 => (0,0)
  | S x => next (decode x)
  end.


Lemma inj_decode : inj decode.
Proof.
  intros n. induction n; intros []; auto.
  - now intros ?%n00_next.
  - now intros ?%eq_sym%n00_next.
  - intros [=?%inj_next%IHn]. congruence.
Qed.

(* show that next is almost surj. *)
Fact zero_or_next : forall p, {a | p = next a} + {p = (0,0)}.
Proof.
  intros [x []].
  - destruct x. now right. left; now exists (0,x).
  - left; now exists (S x, n).
Defined.


Fixpoint Σ n := match n with 0 => 0 | S x => n + Σ x end. 

Definition code '(x,y) := Σ(x+y)+y.

Lemma code_next : forall p, code(next p) = S(code p).
Proof.
  intros [[|x] y]; cbn.
  - rewrite <-!plus_n_O, Nat.add_comm. auto.
  - rewrite !Nat.add_succ_r. cbn. auto.
Qed.

Lemma inv_dc : inv decode code.
Proof.
  unfold inv.
  apply (size_rect code). intros p rec.
  destruct (zero_or_next p) as [[? ->] | ->].
  - rewrite code_next. cbn. f_equal. apply rec.
    rewrite code_next; auto.
  - reflexivity.
Qed.

Fact inv_cd : inv code decode.
Proof.
  intros ?. apply inj_decode. now rewrite inv_dc.
Qed.


Corollary Bij_Nat_NatNat : bijection nat (nat * nat).
Proof.
  exists decode, code. split. apply inv_cd. apply inv_dc.
Qed.


Fact bound x y n : code (x, y) = n -> y < S n.
Proof. cbn. lia. Qed.


Section Cantor.



Section Cantor2.

Definition Cantor x y z := (x + y)*S (x + y) + 2*y = 2*z.
Definition Next x y u v :=
     (x = 0 -> u = S y /\ v = 0) 
  /\ (x <> 0 -> (exists p, S p = x /\ u = p) /\ v = S y).

Fact C01 z :
  Cantor 0 0 z <-> z = 0.
Proof. unfold Cantor; lia. Qed.

Fact C02 x y : 
  Cantor x y 0 <-> x = 0 /\ y = 0.
Proof. unfold Cantor; lia. Qed.

Fact C1 {y z} : 
  Cantor 0 y z <-> Cantor (S y) 0 (S z).
Proof. unfold Cantor; lia. Qed.

Fact C2 {x y z} : 
  Cantor (S x) y z <-> Cantor x (S y) (S z).
Proof. unfold Cantor; lia. Qed.

Lemma Code_Next {x y u v z} :
  Next x y u v -> Cantor x y z <-> Cantor u v (S z).
Proof. 
  unfold Next. destruct x.
  - intros [H _].
    unshelve refine (let H := H _ in _); auto.
    destruct H as [-> ->]. apply C1.
  - intros [_ H].
    unshelve refine (let H := H _ in _); auto.
    destruct H as [[? [<- ->]] ->]. apply C2.
Qed.

Lemma Zero_or_Next u v :
  (u = 0 /\ v = 0) \/ (exists x y, Next x y u v).
Proof.
  destruct v as [|v].
  - destruct u. 
    + now left. 
    + right; exists 0, u. unfold Next. lia.
  - right; exists (S u), v.
    unfold Next. repeat split; try lia.
    now exists u.
Qed.

Lemma Next_inj x y u v u' v' :
  Next x y u v -> Next x y u' v' -> u = u' /\ v = v'.
Proof.
  unfold Next. intros [? H] [? H']. 
  destruct x; [lia|].
  destruct H as [[p [? ->]] ->], H' as [[p' [? ->]] ->]; lia.
Qed.

Fact Cantor_inj1 x y z z' :
  Cantor x y z -> Cantor x y z' -> z = z'.
Proof. unfold Cantor; lia. Qed.


(* This served as a guide for the proof of Cantor_inj2 *)
Goal inj code.
Proof.
  intros a; pattern a; apply (size_rect code).
  intros p rec p'.
  destruct 
    (zero_or_next p) as [[? ->] | ->], 
    (zero_or_next p') as [[? ->] | ->].
  {
    rewrite !code_next. intros [=]. f_equal. apply rec. 
    rewrite code_next. all: auto.
  }
  all: rewrite ?code_next; cbn; auto; lia.
Qed.


Goal inj code.
Proof.
  unfold inj.
  enough (forall n x x', code x = n -> code x' = n -> x = x').
  { 
    intros a b E. eapply H; auto.
  }
  induction n.
  - admit.
  - intros p p'.
    destruct 
    (zero_or_next p) as [[a ->] | ->],
    (zero_or_next p') as [[b ->] | ->].
    { rewrite !code_next. intros [=][=]. f_equal.
      now apply IHn. }
    all: cbn; lia. 
Admitted.


Lemma Cantor_inj2 z :
  forall x x' y y', Cantor x y z -> Cantor x' y' z -> x = x' /\ y = y'.
Proof.
  pattern z; revert z; apply (size_rect id).
  intros z rect u u' v v'.
  destruct 
    (Zero_or_Next u v) as [[-> ->] | [x [y N]] ], 
    (Zero_or_Next u' v') as [[-> ->] | [x' [y' N']] ]. 
  - auto.
  - unfold Cantor; intros ->%C01 ?; lia.
  - unfold Cantor; intros ? ->%C01; lia.
  - destruct z.
    { intros []%C02 []%C02; lia. }
    unshelve refine (fun H H' => 
      let C := proj2 (Code_Next N) H  in
      let C' := proj2 (Code_Next N') H'  in
      let E := rect _ _ _ _ _ _  C C' in _
    ); auto.
    destruct E as [-> ->].
    eapply Next_inj; eauto.
Qed.


Fact Gauss n : {k & n*(S n) = 2*k}.
Proof.
  induction n.
  - now exists 0.
  - destruct IHn as [k ]. 
    exists (n + k + 1); lia.
Defined.

(* Define coding and projection functions *)

Lemma Coding x y : {z & Cantor x y z}.
Proof.
  unfold Cantor.
  destruct (Gauss (x + y)) as [z ].
  exists (z + y); lia.
Defined.

Definition code' x y := projT1 (Coding x y).
Definition code_ x y : Cantor x y (code' x y) := projT2 (Coding x y).

Lemma Decoding z : {x & {y & Cantor x y z}}.
Proof.
  induction z.
  - exists 0, 0. unfold Cantor; lia.
  - destruct IHz as [x [y IH]], x as [|x].
    + eexists; eexists. erewrite <-C1; eauto.
    + eexists; eexists. erewrite <-C2; eauto. 
Defined.

Definition pi1 n := projT1 (Decoding n).
Definition pi2 n := projT1 (projT2 (Decoding n)).
Definition projections n : Cantor (pi1 n) (pi2 n) n := (projT2 (projT2 (Decoding n))).


Lemma code_pi n :
  code' (pi1 n) (pi2 n) = n.
Proof.
  eapply Cantor_inj1.
  apply code_. apply projections.
Qed.

Lemma pi_code x y :
  pi1 (code' x y) = x /\ pi2 (code' x y) = y.
Proof.
  eapply Cantor_inj2.
  apply projections. apply code_.
Qed.



End Cantor2.