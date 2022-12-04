Require Import Lia.
Definition dec P := {P} + {~P}.
Definition EQ X := forall x y : X, {x = y} + {x <> y}.
Definition injective {X Y} (f : X -> Y) := forall a b, f a = f b -> a = b.
Definition surjective {X Y} (f : X -> Y) := forall y, exists x, f x = y.


Fixpoint fin n : Type :=
  match n with 
    0 => False 
  | S n' => option (fin n') 
  end.

Fact EQ_option X :
  EQ X -> EQ (option X).
Proof. intros H [x|][y|]; decide equality. Qed.

Fact EQ_fin n : EQ (fin n).
Proof. induction n. {intros []. } now apply EQ_option. Qed.

Fact dec_exists {n} (p: fin n -> Prop) :
  (forall x, dec (p x)) ->  {x & p x} + (forall x, ~p x).
Proof.
  intros Dec_p. induction n as [|n IH]; auto.
  destruct (IH (fun x => p(Some x)) ltac:(firstorder)) as [[]|]; eauto.
  destruct (Dec_p None); eauto.
  right; intros []; auto.
Defined.


Definition r {X Y} (f : option X -> option (option Y)) x :=
  match f None, f(Some x) with
  | None    , None    => None
  | Some y0 , None    => y0
  | _       , Some y  => y
  end.

Fact r_agree {X Y} f x x' (H : forall x, f(Some x) <> f None) :
  r f x = @r X Y f x' -> f(Some x) = f(Some x').
Proof.
  unfold r.
  destruct  (f (Some x)) eqn:?,
            (f (Some x')) eqn:?,
            (f None) eqn:?; congruence.
Qed.

Fact inj_r {X Y} f :
  injective f -> injective (@r X Y f).
Proof.
  intros Inj x x' [=[]]%r_agree%Inj.
  - reflexivity.
  - intros ? [=]%Inj.
Qed.

Lemma surj_r {X Y} f :
  surjective f -> surjective (@r X Y f).
Proof.
  intros Surj oy.
  destruct (Surj (Some oy)) as [[x|] H].
  - exists x; unfold r.
    destruct (f None), (f (Some x)); congruence.
  - destruct (Surj None) as [[|] H0]; unfold r.
    destruct (f None) as [y0|].
    + exists x. rewrite H0. congruence.
    + exists x. rewrite H in H0. now rewrite H0.
    + exfalso. congruence.
Qed.

Fact trivial_not_inj M (f : fin (S (S M)) -> fin 1) :
  ~ injective f.
Proof.
  intros Inj.
  enough (f None = f(Some None)) as [=]%Inj.
  now destruct (f None) as [[]|],
        (f (Some None)) as [[]|].
Qed.

Lemma inj_ineq M N (f : fin M -> fin N) :
  injective f -> M <= N.
Proof.
  revert M f; induction N.
  all: intros [|M] f Inj; try lia.
  { destruct (f None). }
  destruct N as [|N].
  - destruct M; try lia.
    destruct (trivial_not_inj _ _ Inj).
  - enough (M <= S N) by lia.
    apply (IHN _ (r f)), inj_r, Inj.
Qed.

Lemma ineq_inj M N :
  M <= N -> exists f : fin M -> fin N, injective f.
Proof.
  revert M. induction N.
  all: intros [|M] H; try lia.
  - exists (fun x => x). intros [].
  - exists (fun _ => None). intros [].
  - destruct (IHN M ltac:(lia)) as [f Inj].
    exists (option_rect _ (fun x => Some (f x)) None).
    intros [x|] [x'|][=]; auto.
    rewrite (Inj x x'); congruence.
Qed.

Corollary inj_ineq_equiv M N :
  M <= N <-> exists f : fin M -> fin N, injective f.
Proof.
  split.
  - apply ineq_inj.
  - intros [f Hf]. eapply inj_ineq, Hf.
Qed.

Lemma surj_rneq M N (f : fin M -> fin N) :
  surjective f -> M >= N.
Proof.
  revert M f. induction N.
  all: intros [|M] f Surj; try lia.
  { destruct (Surj None) as [[] ]. }
  enough (M >= N) by lia.
  destruct N as [|N]; try lia.
  eapply IHN, surj_r, Surj.
Qed.

Lemma ineq_surj M N :
  M >= S N -> exists f : fin M -> fin (S N), surjective f.
Proof.
  revert M. induction N; intros [|M]; try lia.
  { intros _. exists (option_rect _ (fun _ => None) None).
    intros [[]|]. exists None. reflexivity. }
  intros HMN. destruct (IHN M ltac:(lia)) as [f Surj].
  exists (option_rect _ (fun x => Some (f x)) None).
  intros [y|].
  - destruct (Surj y) as [x ].
    exists (Some x);cbn. congruence.
  - exists None. reflexivity.
Qed.


Theorem inj_surj N (f : fin N -> fin N) :
  injective f <-> surjective f.
Proof.
  induction N as [|[|N] IH].
  - split; intros ?[].
  - split.
    + intros H [[]|]. exists None.
      now destruct (f None) as [[]|].
    + now intros H [[]|][[]|].
  - specialize (IH (r f)) as [H1 H2]. split.
    + intros Inj%inj_r. 
      assert (surjective (r f)) as Surj by tauto.
      intros [y|].
      * destruct (Surj y) as [x Hx]; fold fin in *.
        exists (Some x).
        admit.
    + intros h%surj_r%H2.
Admitted.