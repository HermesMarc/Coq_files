Require Import Arith Lia.

Definition iffT (X Y : Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).


Definition inj {X Y} (f : X -> Y) :=
  forall x x', f x = f x' -> x = x'.

  Definition inv {X Y} (g : Y -> X) (f : X -> Y) :=
  forall x, g (f x) = x.

Inductive bijection X Y :=
  Bijection (f : X -> Y) g : inv g f -> inv f g -> bijection X Y.

Infix "≅" := (bijection) (at level 60).



Inductive monus (A B : Type) (f : B -> A): Type :=
Monus : inj f -> {a & ~ exists b, f b = a} -> monus A B f.

Arguments Monus {_ _ _}.


Goal forall A B C g, prod A (monus B C g) -> monus (prod A B) (prod A C) (fun p => let (a,c) := p in (a, g c)).
Proof.
  intros A B C g [a [injg [b Hb]]].
  unshelve eexists.
  - intros [][][=<- E].
    apply injg in E. congruence.
  - exists (a, b). intros [[a' c'] [=]].
    apply Hb. now exists c'.
Qed.

Goal forall A B C g, prod A (monus B C g) -> monus (prod A B) (prod A C) (fun p => let (a,c) := p in (a, g c)).
Proof.
