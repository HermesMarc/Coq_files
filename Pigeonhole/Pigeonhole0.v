Require Import Lia.
Definition dec P := {P} + {~P}.
Definition EQ X := forall x y : X, {x = y} + {x <> y}.

Fixpoint fin n : Type :=
  match n with
    0 => False
  | S n' => option (fin n')
  end.

Fact EQ_option X :
  EQ X -> EQ (option X).
Proof. intros H [x|][y|]; decide equality. Defined.

Fact EQ_fin n : EQ (fin n).
Proof. induction n. {intros []. } now apply EQ_option. Defined.

Fact dec_exists {n} (p: fin n -> Prop) :
  (forall x, dec (p x)) ->  {x & p x} + (forall x, ~p x).
Proof.
  intros D. induction n as [|n IH]; auto.
  destruct (IH (fun x => p(Some x)) ltac:(firstorder)) as [[]|]; eauto.
  destruct (D None); eauto.
  right; intros []; auto.
Defined.

Definition Spec {X Y} (f : option X -> option Y) x r_x :=
  match f None, f(Some x) with
  | None    , _       => f(Some x) = Some r_x
  | Some y0 , None    => r_x = y0
  | Some y0 , Some y  => r_x <> y0 /\ r_x = y
  end.

Definition R {X Y} (f : option X -> option Y) :
  (forall x, f(Some x) <> f None) -> forall x, { r_x & Spec f x r_x}.
Proof.
  unfold Spec; intros H x.
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
let r := r f H in
  r x = r x' -> f(Some x) = f(Some x').
Proof.
  unfold r; intros e.
  generalize (r_spec f H x), (r_spec f H x').
  rewrite <-e.
  generalize (projT1 (R f H x)) as z.
  intros ?. clear e; unfold Spec.
  destruct (f None) as [y0|]. 2: congruence.
  destruct  (f (Some x)) as [y|],
            (f (Some x')) as [y'|].
  * intros [][]; subst; congruence.
  * intros [] ?; subst; congruence.
  * intros ? []; subst; congruence.
  * intros [][]; reflexivity.
Qed.

Lemma Pigeonhole M N (f : fin M -> fin N) :
  M > N -> {a &{b & a <> b /\ f a = f b}}.
Proof.
  revert M f. induction N.
  { intros [] f; [lia | destruct (f None)]. }
  intros [|M] f H_NM; try lia.
  destruct (dec_exists (fun x => f(Some x) = f None)) as [H|H].
  { intros ?; apply EQ_fin. }
  - destruct H as [x ]. exists (Some x), None.
    split; congruence.
  - destruct (IHN _ (r f H) ltac:(lia)) as (x & x' &[]).
    exists (Some x), (Some x').
    split; try congruence.
    eapply r_agree; eauto.
Qed.