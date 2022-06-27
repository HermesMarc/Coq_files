Require Import ConstructiveEpsilon.
Definition WO_nat := constructive_indefinite_ground_description_nat.

Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.
Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
Notation p1 := projT1.
Notation p2 := projT2.

Definition LEM := forall X, X \/ ~X.

Definition stable P := ((P -> False) -> False) -> P.

Definition dec (P : Prop) := {P} + {~P}. 
Definition Dec {X} p := forall x : X, dec (p x).

Definition sdec (P : Prop) := exists (f : nat -> bool), P <-> exists n, f n = true.
Definition Sdec {X} p := exists (f : nat -> X -> bool), forall x, p x <-> exists n, f n x = true.
Definition enum {X} p := exists f, forall x : X, p x <-> exists n : nat, f n = Some x.

Definition Enum X := Sigma f, forall x : X, exists n : nat, f n = Some x. 
Definition EQ X := forall x y : X, dec (x = y).
Definition AP X := forall x y : X, dec (~ x = y).

Definition surj {X Y} (f : X -> Y) := forall y, exists x, f x = y.
Definition inj {X Y} (f : X -> Y) := forall x x', f x = f x' -> x = x'.
Definition inv {X Y} (g: Y -> X) (f: X -> Y) := forall x, g (f x) = x.

Inductive Bij (X Y : Type) : Type :=
| Bijection: forall (f: X -> Y) (g: Y -> X), inv f g -> inv g f -> Bij X Y.
Arguments Bijection {X Y}.



Lemma Skolem {X Y} (R : X -> Y -> Prop) : 
  (forall x, Sigma y, R x y) -> Sigma f, forall x, R x (f x).
Proof.
  intros H. unshelve eexists; intros x; cbn; now destruct (H x) as [y ].
Defined.


Module DN.
Definition ret {A : Prop} : A -> ~~A.                     tauto. Defined.
Definition bind {A B : Prop} : ~~A -> ~~(A -> B) -> ~~B.  tauto. Defined.
Definition remove {A B} : ~~A -> (A -> ~B) -> ~B.         tauto. Defined.
Definition lem X : ~~(X \/ ~X).                           tauto. Defined.
Definition dn X : ~~(~~X -> X).                           tauto. Defined.

Ltac lem_ H := apply (bind (lem H)); try tauto.
End DN.