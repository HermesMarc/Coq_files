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
  intros dec_p. induction n as [|n IH]; auto.
  destruct (IH (fun x => p(Some x)) ltac:(firstorder)) as [[]|]; eauto.
  destruct (dec_p None); eauto.
  right; intros []; auto.
Defined.

Definition r {X Y} (f : option X -> option (option Y)) x :=
  match f None, f(Some x) with
  | None    , None    => None
  | Some y0 , None    => y0
  | _       , Some y  => y
  end.

Definition pair {X Y} (f : X -> Y) a := {b : X & a <> b /\ f a = f b}.

Section Facts.
Context {X Y : Type} (f : option X -> option (option Y)).
Hypothesis (H : forall x, f(Some x) <> f None). 

Fact r_agree x x' :
  r f x = r f x' -> f(Some x) = f(Some x').
Proof. 
  unfold r. destruct
  (f (Some x))  eqn:?,
  (f (Some x')) eqn:?,
  (f None)      eqn:?; congruence.
Qed.

Fact related_pair : 
  sigT (pair (r f)) -> sigT (pair f).
Proof.
  intros (a & b & []).
  exists (Some a), (Some b).
  split; try congruence.
  eapply r_agree; eauto.
Qed.

Fact trivial_pair (g : option (option X) -> fin 1) :
  sigT (pair g).
Proof.
  exists None, (Some None).
  split; try congruence.
  now destruct (g None) as [[]|],
        (g (Some None)) as [[]|].
Qed.
End Facts.

Lemma Pigeonhole M N (f : fin M -> fin N) :
  M > N -> sigT (pair f).
Proof.
  revert M f. induction N.
  all: intros [|M] f MN; try lia.
  { destruct (f None). }
  destruct N as [|N].
  { destruct M; try lia. apply trivial_pair. }
  destruct (dec_exists (fun x => f(Some x) = f None)) as [[x ]|H].
  - intros ?; apply EQ_fin.
  - exists (Some x), None. split; congruence.
  - apply related_pair, IHN; apply H || lia.
Defined.