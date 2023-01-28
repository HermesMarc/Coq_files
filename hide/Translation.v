(*

  The definition of First-Oder Logic used here is adapted from 
  the following library: https://github.com/uds-psl/coq-library-undecidability/

*)


Require Import Vector List Lia.

Require Import Coq.Vectors.Vector.
Definition vec := t.

Require Import Equations.Equations.
Require Import List.

Notation "x 'el' A" := (In x A) (at level 70).
Notation "A '<<=' B" := (incl A B) (at level 70).


Local Set Implicit Arguments.

Inductive flavor := class | intu | peirce | min.
Existing Class flavor.

Section ND_def.

  Implicit Type fl : flavor.
  Reserved Notation "A ⊢ phi" (at level 61).

  (* Definition of natural deduction for minimal logic *)

  Inductive prop : Type := 
  | Bot : prop
  | P : nat -> prop
  | Conj : prop -> prop -> prop
  | Disj : prop -> prop -> prop
  | Imp : prop -> prop -> prop.


  Declare Scope syn.
  Open Scope syn.

  Notation "⊥" := (Bot) : syn.
  Notation "A ∧ B" := (Conj A B) (at level 41) : syn.
  Notation "A ∨ B" := (Disj A B) (at level 42) : syn.
  Notation "A '-->' B" := (Imp A B) (at level 43, right associativity) : syn.
  Notation "A '<-->' B" := ((A --> B) ∧ (B --> A)) (at level 43) : syn.
  
  Inductive prv : forall fl, list prop -> prop -> Type :=
  | II {fl} A phi psi : phi::A ⊢ psi -> A ⊢ (phi --> psi)
  | IE {fl} A phi psi : A ⊢ phi --> psi -> A ⊢ phi -> A ⊢ psi
  | Ctx {fl} A phi : phi el A -> A ⊢ phi
  | CI {fl} A phi psi : A ⊢ phi -> A ⊢ psi -> A ⊢ phi ∧ psi
  | CE1 {fl} A phi psi : A ⊢ phi ∧ psi -> A ⊢ phi
  | CE2 {fl} A phi psi : A ⊢ phi ∧ psi -> A ⊢ psi
  | DI1 {fl} A phi psi : A ⊢ phi -> A ⊢ phi ∨ psi
  | DI2 {fl} A phi psi : A ⊢ psi -> A ⊢ phi ∨ psi
  | DE {fl} A phi psi theta : A ⊢ phi ∨ psi -> phi::A ⊢ theta -> psi::A ⊢ theta -> A ⊢ theta
  | DNE A phi : prv class A ((phi --> ⊥) --> ⊥) -> prv class A phi
  | Exp A phi : prv intu A ⊥ -> prv intu A phi
  | PL A phi psi : prv peirce A (((phi --> psi) --> phi) --> phi)
  where "A ⊢ phi" := (prv _ A phi).

End ND_def.

Arguments prv {_} _ _.
Notation "A ⊢ phi" := (prv A phi) (at level 55).
Notation "A ⊢C phi" := (@prv class A phi) (at level 55).
Notation "A ⊢I phi" := (@prv intu A phi) (at level 55).
Notation "A ⊢M phi" := (@prv min A phi) (at level 55).
Notation "A ⊢P phi" := (@prv peirce A phi) (at level 55).

