Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.
Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
Notation p1 := projT1.
Notation p2 := projT2.

Definition dec (P : Type) := (P + (P -> False))%type. 
Definition Dec {X} p := forall x : X, dec (p x).

Definition EQ X := forall x y : X, dec (x = y).

Definition surj {X Y} (f : X -> Y) := forall y, exists x, f x = y.
Definition inj {X Y} (f : X -> Y) := forall x x', f x = f x' -> x = x'.
Definition inv {X Y} (g: Y -> X) (f: X -> Y) := forall x, g (f x) = x.

Inductive Bij (X Y : Type) : Type :=
| Bijection: forall (f: X -> Y) (g: Y -> X), inv f g -> inv g f -> Bij X Y.
Arguments Bijection {X Y}.