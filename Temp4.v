Require Import Lia.

Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.
Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
Notation p1 := projT1.
Notation p2 := projT2.

Definition dec P := sum P (P -> False).
Definition EQ X := forall x y : X, dec (x = y).

Definition inv {X Y} (g: Y -> X) (f: X -> Y) := forall x, g (f x) = x.
Inductive Bij (X Y : Type) : Type :=
| Bijection: forall (f: X -> Y) (g: Y -> X), inv f g -> inv g f -> Bij X Y.
Arguments Bijection {X Y}.


Fact EQ_option X :
  EQ X -> EQ (option X).
Proof. 
  intros H [x|][y|]; try ((left + right); congruence).
  destruct (H x y); (left + right); congruence.
Defined.

Lemma Rewire X Y f g (gf : inv g f) :
  forall x : X, Sigma y : Y,
    match f (Some x) with
      Some y' => y = y'
    | None => f None = Some y 
    end.
Proof.
  intros x; destruct (f (Some x)) as [y|] eqn:?.
  - now exists y.
  - destruct (f None) as [y|] eqn:?.
    + now exists y.
    + exfalso. congruence.
Qed.
Arguments Rewire {_ _ _ _}.

Lemma Rewire_inv {X Y} (f : option X -> option Y) g (fg : inv f g) (gf : inv g f) : 
  inv (fun y => p1 (Rewire fg y)) (fun x => p1 (Rewire gf x)).
Proof.
  intros x.
  destruct (Rewire gf x) as [y ]; cbn.
  destruct (Rewire fg y) as []; cbn.
  destruct  (f (Some x)) as [] eqn:?,
            (g (Some y)) as [] eqn:?;
  congruence.
Qed.

Lemma option_inj X Y :
  Bij (option X) (option Y) -> Bij X Y.
Proof.
  intros [].
  eexists; apply Rewire_inv.
  Unshelve. all: eassumption.
Qed.


Section Fin.
Variable F : Type.

Fixpoint Fin n : Type :=
  match n with
    0 => F
  | S n' => option (Fin n')
  end.

Definition d X := sum X (X -> F).
Definition D {X} p := forall x:X, d (p x).

Fact dec_exists {n} (p: Fin n -> Prop) :
  D p -> {x & p x} + (forall x, p x -> F).
Proof.
  intros Dec_p. induction n as [|n IH]; auto.
  destruct (IH (fun x => p(Some x)) ltac:(firstorder)) as [[]|]; eauto.
  destruct (Dec_p None); eauto.
  right; intros []; eauto.
Defined.
End Fin.

Lemma Fin_comp F n m :
  Fin (Fin F m) n = Fin F (n + m).
Proof.
Admitted.






Definition r {X Y} (f : option X -> option Y) esc : X -> Y :=
fun x =>
  match f None, f(Some x) with
  | None    , None    => esc
  | Some y0 , None    => y0
  | _       , Some y  => y
  end.

Lemma r_agree {X Y} esc f x x' (H : forall x, f(Some x) <> f None) :
let r := @r X Y f esc in
  r x = r x' -> f(Some x) = f(Some x').
Proof.
  unfold r.
  destruct  (f (Some x)) eqn:?,
            (f (Some x')) eqn:?,
            (f None) eqn:?; congruence.
Qed.

Definition fin n := Fin False n.

Fact EQ_fin n : EQ (fin n).
Proof. induction n. {intros []. } now apply EQ_option. Defined.

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
  destruct (dec_exists False (fun x => f(Some x) = f None)) as [[x ]|H].
  { intros ?. unfold d. apply EQ_fin. }
  - exists (Some x), None. split; congruence.
  - destruct (IHN M (r f None) ltac:(lia)) as (x & x' &[]).
    exists (Some x), (Some x').
    split; try congruence.
    eapply r_agree; eauto.
Defined.







Fixpoint sum {n} :=
  match n return (fin n -> nat) -> nat with
    0 => fun _ => 0
  | S m => fun f => f None + sum (fun x => f(Some x))
  end.

Lemma bounded n f :
  forall x : fin n, f x <= sum f.
Proof.
  induction n as [|n IH].
  - intros [].
  - intros [x|].
    + specialize (IH (fun x => f(Some x)) x).
      cbn in IH.
      Set Printing All.
      change (@sum (S n) f) with (f None + sum (fun x => f(Some x))).
      Set Printing All.
      lia.
Qed.

Lemma nat_not_finite' :
  (Sigma n, Bijection nat (Fin n)) -> False.
Proof.
  intros [n [f g _ gf]].
  destruct (bounded _ g) as [m H].
  specialize (H (f (S m))).
  rewrite gf in H. lia.
Qed.