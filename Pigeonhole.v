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

Lemma r_agree {X Y} f x x' (H : forall x, f(Some x) <> f None) :
let r := @r X Y f in
  r x = r x' -> f(Some x) = f(Some x').
Proof.
  unfold r.
  destruct  (f (Some x)) eqn:?,
            (f (Some x')) eqn:?,
            (f None) eqn:?; congruence.
Qed.

Fact trivial_Pigeonhole M (f : fin (S M) -> fin 1) :
  S M > 1 -> {a &{ b & a <> b /\ f a = f b}}.
Proof.
  intros ?. destruct M; try lia.
  exists None, (Some None).
  split; try congruence.
  now destruct (f None) as [[]|],
        (f (Some None)) as [[]|].
Qed.

Lemma Pigeonhole M N (f : fin M -> fin N) :
  M > N -> {a &{ b & a <> b /\ f a = f b}}.
Proof.
  revert M f. induction N.
  all: intros [|M] f Surj; try lia.
  { destruct (f None). }
  destruct N as [|N].
  { now apply trivial_Pigeonhole. }
  destruct (dec_exists (fun x => f(Some x) = f None)) as [[x ]|H].
  { intros ?; apply EQ_fin. }
  - exists (Some x), None. split; congruence.
  - destruct (IHN M (r f) ltac:(lia)) as (x & x' &[]).
    exists (Some x), (Some x').
    split; try congruence.
    eapply r_agree; eauto.
Defined.