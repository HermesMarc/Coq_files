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
Proof. intros H [x|][y|]; decide equality. Qed.

Fact EQ_fin n : EQ (fin n).
Proof. induction n. {intros []. } now apply EQ_option. Qed.

Fact dec_exists {n} (p: fin n -> Prop) :
  (forall x, dec (p x)) -> (exists x, p x) + (forall x, ~p x).
Proof.
  intros Hdec. induction n as [|n IH].
  {right; intros []. }
  specialize (IH (fun a => p (Some a))) as [IH|IH].
  { intros ?; apply Hdec. }
  - left. destruct IH as [a H].
    exists (Some a). apply H.
  - destruct (Hdec None) as [H|H].
    * left. exists None. apply H.
    * right. intros [a|]. exact (IH a). exact H.
Qed.

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
  S M > 1 -> exists a b, a <> b /\ f a = f b.
Proof.
  intros ?. destruct M; try lia. 
  exists None, (Some None).
  split; try congruence.
  now destruct (f None) as [[]|],
        (f (Some None)) as [[]|].
Qed.

Lemma Pigeonhole M N (f : fin M -> fin N) :
  M > N -> exists a b, a <> b /\ f a = f b.
Proof.
  revert M f. induction N.
  all: intros [|M] f Surj; try lia.
  { destruct (f None). }
  destruct N as [|N].
  { now apply trivial_Pigeonhole. }
  destruct (dec_exists (fun x => f(Some x) = f None)) as [H|H].
  { intros ?; apply EQ_fin. }
  - destruct H as [x ]. exists (Some x), None.
    split; congruence.
  - destruct (IHN M (r f) ltac:(lia)) as (x & x' &[]).
    exists (Some x), (Some x').
    split; try congruence.
    eapply r_agree; eauto.
Qed.