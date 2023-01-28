(*

  The definition of First-Oder Logic used here is adapted from 
  the following library: https://github.com/uds-psl/coq-library-undecidability/

*)


Require Import Vector List Lia.

Require Import Coq.Vectors.Vector.
Definition vec := t.

Require Import List.

Notation "x 'el' A" := (In x A) (at level 70).
Notation "A '<<=' B" := (incl A B) (at level 70).

Local Set Implicit Arguments.

Inductive flavor := class | intu.
Existing Class flavor.

Inductive prop : Type :=
| Bot : prop
| P : nat -> prop
| Imp : prop -> prop -> prop.


Declare Scope syn.
Open Scope syn.

Notation "⊥" := (Bot) : syn.
Notation "A '-->' B" := (Imp A B) (at level 43, right associativity) : syn.



Section ND_def.

  Implicit Type fl : flavor.
  Reserved Notation "A ⊢ phi" (at level 61).

  (* Definition of natural deduction for minimal logic *)
  
  Inductive prv : forall fl, list prop -> prop -> Type :=
  | II {fl} A phi psi : phi::A ⊢ psi -> A ⊢ (phi --> psi)
  | IE {fl} A phi psi : (phi --> psi) el A -> A ⊢ phi -> A ⊢ psi
  | Ctx {fl} A phi : phi el A -> A ⊢ phi
  | DNE A phi : prv class A ((phi --> ⊥) --> ⊥) -> prv class A phi
  | Exp A phi : prv intu A ⊥ -> prv intu A phi
  where "A ⊢ phi" := (prv _ A phi).

End ND_def.

Arguments prv {_} _ _.
Notation "A ⊢ phi" := (prv A phi) (at level 55).
Notation "A ⊢C phi" := (@prv class A phi) (at level 55).
Notation "A ⊢I phi" := (@prv intu A phi) (at level 55).

Ltac Select n := 
  match n with 
  | 0 => left
  | S ?x => right; Select x
  end.
Ltac Exact n := apply Ctx; now Select n.
Ltac Apply n := eapply IE; [now Select n|idtac].
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
End Testing.

Fixpoint rm_DN ϕ : prop :=
  match ϕ with
  | (α --> ⊥) --> ⊥ => rm_DN α
  | (α --> β) => α --> rm_DN β
  | _ => ϕ
  end.

Fact dec_prop_eq (α β : prop) :
  {α = β} + {α <> β}.
Proof. repeat decide equality. Qed.

Fact rm_DN_no_neg α β :
  β <> ⊥ -> rm_DN (α --> β) = α --> rm_DN β.
Proof.
  intros ?. destruct β; try congruence.
  all: now destruct α as [| |? []].
Qed.


Lemma Extraction Γ ϕ :
  Γ ⊢C ϕ -> { ψ & prod (Γ ⊢C ψ --> ϕ)(Γ ⊢I ψ) }.
Proof.
  induction 1 as [fl Γ α β H IH|fl Γ α β H1 H2 IH|??? H|??? IH| ].
  - destruct IH as [ψ [e Hψ]].
    exists (α --> ((β --> ⊥) --> ⊥)). split.
    2: { Intros. Apply 0. (* weakening *) admit. }
    Intros. (* weakening *) admit.
  - destruct IH1 as [α_β H], IH2 as [α' H'].
    (*  Conjunction is needed here to put in the
        formula α' ∧ α_β. *) admit.
  - exists phi. repeat split. 
    Intros; Exact 0. apply Ctx, H.
  - destruct IH as [ψ Hψ]. exists ψ.
    split. Intro. apply DNE. (* nee weakening *) admit.
    apply Hψ.
  - exists phi. repeat split. 
    Intro; Exact 0. now apply Exp.
Admitted.