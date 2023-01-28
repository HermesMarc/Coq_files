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

Inductive prop : Type :=
| Bot : prop
| P : nat -> prop
| Conj : prop -> prop -> prop
| Imp : prop -> prop -> prop.


Declare Scope syn.
Open Scope syn.

Notation "⊥" := (Bot) : syn.
Notation "A ∧ B" := (Conj A B) (at level 41) : syn.
Notation "A '-->' B" := (Imp A B) (at level 43, right associativity) : syn.
Notation "A '<-->' B" := ((A --> B) ∧ (B --> A)) (at level 43) : syn.


Section ND_def.

  Implicit Type fl : flavor.
  Reserved Notation "A ⊢ phi" (at level 61).

  (* Definition of natural deduction for minimal logic *)
  
  Inductive prv : forall fl, list prop -> prop -> Type :=
  | II {fl} A phi psi : phi::A ⊢ psi -> A ⊢ (phi --> psi)
  | IE {fl} A phi psi : A ⊢ phi --> psi -> A ⊢ phi -> A ⊢ psi
  | Ctx {fl} A phi : phi el A -> A ⊢ phi
  | CI {fl} A phi psi : A ⊢ phi -> A ⊢ psi -> A ⊢ phi ∧ psi
  | CE1 {fl} A phi psi : A ⊢ phi ∧ psi -> A ⊢ phi
  | CE2 {fl} A phi psi : A ⊢ phi ∧ psi -> A ⊢ psi
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

Ltac Select n := 
  match n with 
  | 0 => left
  | S ?x => right; Select x
  end.
Ltac Exact n := apply Ctx; now Select n.
Ltac Apply n := eapply IE; [Exact n|idtac].
Ltac Intro := apply II.
Ltac Intros := repeat Intro.


Section Testing.
Variable fl : flavor.
Variable p q s : prop.

Goal nil ⊢ p --> p.
Proof. Intro. Exact 0. Qed.

Example cl_pierce :
  nil ⊢C ((p --> q) --> p) --> p.
Proof.
  apply DNE. Intro; Apply 0.
  Intro. Apply 0.
  apply II, DNE, II. Apply 3.
  Intro. Exact 2.
Qed.

Goal nil ⊢ (p ∧ q --> s) <--> (p --> q --> s).
Proof.
  apply CI. 
  - Intros. Apply 2. apply CI.
    + Exact 1.
    + Exact 0.
  - Intros. eapply IE. Apply 1.
    + eapply CE1. Exact 0.
    + eapply CE2. Exact 0.
Qed.

End Testing.