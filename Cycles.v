Require Import Lists.List Lia.
Import ListNotations.
Notation "x 'el' A" := (In x A) (at level 70).
Notation "x 'nel' A" := (~ In x A) (at level 70).
Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.
Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).


Definition dec P := {P} + {~P}.
Definition decT P := sum P (P -> False).
Definition EQ X := forall x y : X, {x = y} + {x <> y}.

Fixpoint iter {X: Type} (f: X -> X) (n:nat) (x:X) : X :=
  match n with
  | 0 => x
  | S n => f (iter f n x)
  end.

Fixpoint fin n : Type :=
  match n with 
    0 => False 
  | S n' => option (fin n') 
  end.

Fact EQ_option X :
  EQ X -> EQ (option X).
Proof.
  intros H [x|][y|]; decide equality.
Defined.

Fact EQ_fin n : EQ (fin n).
Proof.
  induction n.
  - intros [].
  - now apply EQ_option.
Defined.

Fact fin_dec_pred {n} (p: fin n -> Prop) :
  (forall x, dec (p x)) -> (forall x, ~p x) + (exists x, p x).
Proof.
  intros Hdec. induction n as [|n IH].
  {left; intros []. }
  specialize (IH (fun a => p (Some a))) as [IH|IH].
  { intros ?; apply Hdec. }
  - destruct (Hdec None) as [H|H].
    * right. exists None. apply H.
    * left. intros [a|]. exact (IH a). exact H.
  - right. destruct IH as [a H].
    exists (Some a). apply H.
Qed.

Definition R {X Y} (f : option X -> option Y) :
  (forall x, f(Some x) <> f None) ->
  forall x, { r_x &
    match f None, f(Some x) with
    | None    , _       => f(Some x) = Some r_x
    | Some y0 , None    => r_x = y0
    | Some y0 , Some y  => r_x <> y0 /\ r_x = y
    end}.
Proof.
  intros H x.
  destruct  (f None) as [y0|] eqn:?, 
            (f (Some x)) as [y|] eqn:?.
  - exists y. split; congruence.
  - exists y0. reflexivity.
  - exists y. reflexivity.
  - exfalso. now apply (H x).
Defined.

Definition r {X Y} (f : option X -> option Y) H x := projT1 (R f H x).
Definition r_spec {X Y} (f : option X -> option Y) H x := projT2 (R f H x).

Lemma r_agree {X Y} (f : option X -> option Y) H x x' : 
let r_ := r f H in
  x <> x' -> r_ x = r_ x' -> f(Some x) = f(Some x').
Proof.
  unfold r; intros ne e.
  generalize (r_spec f H x), (r_spec f H x').
  rewrite <-e.
  generalize (projT1 (R f H x)) as z; fold fin.
  intros ?. clear e; cbn in *. pattern (f None).
  destruct (f None) as [y0|].
  2: congruence.
  destruct  (f (Some x)) as [y|], 
            (f (Some x')) as [y'|].
  * intros [][]; subst; congruence.
  * intros [] ?; subst; congruence.
  * intros ? []; subst; congruence.
  * congruence.
Qed.

Lemma Pigeonhole M N (f : fin M -> fin N) :
  M > N -> exists a b, a <> b /\ f a = f b.
Proof.
  revert M f. induction N.
  {intros [] f; [lia | destruct (f None)]. }
  intros [|M] f H_NM; try lia.
  destruct (fin_dec_pred (fun x => f (Some x) = f None)) as [h|h].
  { intros ?; apply EQ_fin. }
  - destruct (IHN _ (r f h) ltac:(lia)) as (x & x' & ne & e).
    exists (Some x), (Some x').
    split; try congruence.
    eapply r_agree; eauto.
  - destruct h as [x Hx]. exists (Some x), None.
    split; congruence.
Qed.


Definition fin2nat {n} (x : fin n) : nat.
Proof.
  induction n as [|n f_n]; [destruct x|].
  destruct x as [y|].
  - refine (S (f_n y)).
  - exact 0.
Defined.

Fact inj_fin2nat {n} (x y : fin n) :
  fin2nat x = fin2nat y -> x = y.
Proof.
  revert x y. induction n. {intros []. }
  intros [x|][y|][=]; try rewrite (IHn x y).
  all: congruence.
Qed.

Fact bound_fin2nat {n} (x : fin n) :
  fin2nat x < n.
Proof.
  revert x. induction n. {intros []. }
  intros [x|].
  - change (S (fin2nat x) < S n).
    specialize (IHn x); lia.
  - cbn; lia.
Qed.


Lemma cycle {N} f (x : fin N) :
  exists k c, c + k <= N /\ c > 0 /\ iter f (c + k) x = iter f k x.
Proof.
  destruct N as [|N].
  { destruct x. }
  destruct (Pigeonhole (S (S N)) (S N) 
    (fun n => iter f (fin2nat n) x) ltac:(lia)) as (a&b&H).
  remember (fin2nat a) as n.
  remember (fin2nat b) as m.
  assert (n = m \/ n < m \/ n > m) as [->|[h|h]] by lia.
  {exfalso. apply H. apply inj_fin2nat. congruence. }
  - exists n, (m - n). 
    specialize (bound_fin2nat b) as B.
    repeat split; try lia.
    replace (m - n + n) with m by lia. 
    symmetry. apply H.
  - exists m, (n - m). 
    specialize (bound_fin2nat a) as B.
    repeat split; try lia.
    replace (n - m + m) with n by lia. 
    apply H.
Qed.

Fact iter_hom {X f} n m {x:X} :
  iter f (n + m) x = iter f n (iter f m x).
Proof.
  induction n.
  - reflexivity.
  - cbn. now f_equal.
Qed.

Lemma reduce_once {X} n k m f (x:X) :
  iter f (k + m) x = iter f m x -> m <= n -> iter f (k + n) x = iter f n x.
Proof.
  intros Hm Hmn.
  replace (k + n) with ((n - m) + (k + m)) by lia.
  rewrite iter_hom, Hm, <-iter_hom.
  now replace (n - m + m) with n by lia.
Qed.

Lemma reduce_all {X} n k m d f (x:X) :
  iter f (k + m) x = iter f m x -> m <= n -> iter f (k*d + n) x = iter f n x.
Proof.
  induction d.
  - now replace (k*0 + n) with n by lia.
  - intros H1 H2. cbn.
    replace (k*(S d) + n) with (k + (k*d + n)) by lia.
    rewrite iter_hom, (IHd H1 H2), <-iter_hom.
    eapply reduce_once; eauto.
Qed.

Notation "a \ b" := (exists x, a * x = b) (at level 42).

Lemma Generalized n f (x : fin (S n)) a :
  (forall k, k <= (S n) -> k \ a) -> iter f (a + n) x = iter f n x.
Proof.
  intros Hdiv_a.
  destruct (cycle f x) as (k & c & H1&H2&H3).
  destruct (Hdiv_a c ltac:(lia)) as [d <-].
  eapply reduce_all with k; auto. lia.
Qed.