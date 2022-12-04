From Coq Require Import List.
Import ListNotations.


Definition iffT (X Y : Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).

(* Minimal Logic *)
Section Minimal.

  Inductive prop : Type :=
  | P : nat -> prop
  | Impl : prop -> prop -> prop
  | Conj : prop -> prop -> prop
  | Disj : prop -> prop -> prop.

  Notation "A ∧ B" := (Conj A B) (at level 41).
  Notation "A ∨ B" := (Disj A B) (at level 42).
  Notation "A '-->' B" := (Impl A B) (at level 43, right associativity).
  Notation "x 'el' A" := (In x A) (at level 70).
  Notation "A <<= B" := (incl A B) (at level 70).

  (* Inductive type formalizing deduction in minimal logic *)
  Reserved Notation "A ⊢ s" (at level 70).
  Inductive prv : list prop -> prop -> Type :=
  | II A phi psi : phi::A ⊢ psi -> A ⊢ phi --> psi
  | IE A phi psi : A ⊢ phi --> psi -> A ⊢ phi -> A ⊢ psi
  | Ctx A phi : phi el A -> A ⊢ phi
  | CI A phi psi : A ⊢ phi -> A ⊢ psi -> A ⊢ phi ∧ psi
  | CE1 A phi psi : A ⊢ phi ∧ psi -> A ⊢ phi
  | CE2 A phi psi : A ⊢ phi ∧ psi -> A ⊢ psi
  | DI1 A phi psi : A ⊢ phi -> A ⊢ phi ∨ psi
  | DI2 A phi psi : A ⊢ psi -> A ⊢ phi ∨ psi
  | DE  A phi psi theta : A ⊢ phi ∨ psi -> phi::A ⊢ theta -> psi::A ⊢ theta -> A ⊢ theta
  where "A ⊢ phi" := (prv A phi).

  Ltac Select n :=
    match n with 
    | 0 => left
    | S ?x => right; Select x
    end.
  Ltac Exact n := apply Ctx; now Select n.
  Ltac Intro := apply II.
  Ltac Intros := repeat Intro.
  Ltac Apply n := eapply IE; [Exact n|idtac].
  Ltac Left := apply DI1.
  Ltac Right := apply DI2.
  Ltac Destruct n := eapply DE; [Exact n|idtac|idtac].
  Ltac Split := apply CI.


  Lemma Weak A B phi :
    A ⊢ phi -> A <<= B -> B ⊢ phi.
  Proof.
    induction 1 in B |-*; try unshelve (solve [econstructor; intuition]); try now econstructor.
  Qed.

  Fact Imp A s t :
    A ⊢ s --> t <=> s::A ⊢ t.
  Proof.
    split.
    - intros H. eapply IE. 
      2: apply Ctx. eapply Weak. exact H.
      all: firstorder.
    - now Intro.
  Qed.



  (* Fix some propositional variable F *)
  Variable F : prop.

  Definition Contradiction := forall A B, nil ⊢ A --> (A --> F) --> B.
  Definition Explosion := forall A, nil ⊢ F --> A.
  Definition LEM := forall A, nil ⊢ A ∨ (A --> F).
  Definition DN := forall A, nil ⊢ ((A --> F) --> F) --> A.
  Definition CP := forall A B, nil ⊢ ((B --> F) --> (A --> F)) --> A --> B.

  Definition Peirce := forall A B, nil ⊢ ((A --> B) --> A) --> A.


  Lemma CP' {X Y Gamma} : CP -> Gamma ⊢ (Y --> F) --> (X --> F) -> Gamma ⊢ X --> Y.
  Proof.
    intros cp. apply IE. eapply Weak.
    apply (cp X Y). firstorder.
  Qed.

  Goal DN <=> CP.
  Proof.
    split.
    - intros dn A B.
      generalize (dn B).
      eapply IE. Intros.
      Apply 2. Intros.
      eapply IE. instantiate (1 := A).
      + Apply 2. Exact 0.
      + Exact 1.
    - intros cp A. apply (CP' cp).
      Intros. Apply 0. Intros.
      Apply 2. Exact 0.
  Qed.

  Goal DN -> Explosion.
  Proof.
    intros dn A.
    generalize (dn A).
    eapply IE. Intros.
    Apply 1. Intros. Exact 1.
  Qed.

  Goal CP -> Peirce.
  Proof.
    intros cp A B. apply (CP' cp).
    Intros. Apply 1. Apply 0.
    apply (CP' cp). Intro. Exact 2.
  Qed.

  Goal Peirce -> LEM.
  Proof.
    intros peirce X.
    eapply IE. apply (peirce (X ∨ (X --> F)) F).
    Intros. Right. Intros.
    Apply 1. Left. Exact 0.
  Qed.
  
  Goal LEM * Explosion -> DN.
  Proof.
    intros [lem expl] X.
    generalize (lem X); apply IE.
    generalize (expl X); apply IE.
    Intros. Destruct 1.
    - Exact 0.
    - Apply 3. Apply 1. Exact 0.
  Qed.


  Section NonDeduc.

    (*  Meta Argument: Assume it is possible to show 
        Peirce -> Explosion = forall X, |- F -> X. 
        Since F was an arbitrary choice, this would mean we would really have a way of showing : 
     *)
    Hypothesis H : forall Y, Peirce -> forall X, nil ⊢ Y --> X.

    (* However it then turns out that *)
    Goal Peirce -> forall P, nil ⊢ P.
    Proof.
      intros peirce P.
      enough (nil ⊢ (P --> P) --> P) as C.
      revert C. eapply IE. 
      - Intros. Apply 0. Intros. Exact 0.
      - now apply H.
    Qed.
       
  End NonDeduc.


End Minimal.


