(*

  The definition of First-Oder Logic used here is adapted from 
  the following library: https://github.com/uds-psl/coq-library-undecidability/

*)


Require Import Vector List Lia.

Require Import Coq.Vectors.Vector.
Definition vec := t.

Require Import Equations.Equations.


(* Some preliminary definitions for substitions  *)
Definition scons {X: Type} (x : X) (xi : nat -> X) :=
  fun n => match n with
        | 0 => x
        | S n => xi n
        end.

Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y)  :=
  fun x => g (f x).

(* Signatures are a record to allow for easier definitions of general transformations on signatures *)

Class funcs_signature :=
  { syms : Type; ar_syms : syms -> nat }.

Coercion syms : funcs_signature >-> Sortclass.

Class preds_signature :=
  { preds : Type; ar_preds : preds -> nat }.

Coercion preds : preds_signature >-> Sortclass.

Section fix_signature.

  Context {Σ_funcs : funcs_signature}.

  Unset Elimination Schemes.

  Inductive term  : Type :=
  | var : nat -> term
  | func : forall (f : syms), vec term (ar_syms f) -> term.

  Set Elimination Schemes.

  Fixpoint subst_term (σ : nat -> term) (t : term) : term :=
    match t with
    | var t => σ t
    | func f v => func f (map (subst_term σ) v)
    end.

  Context {Σ_preds : preds_signature}.

  (* Syntax is parametrised in binary operators and quantifiers. *)
  Class operators := {binop : Type ; quantop : Type}.
  Context {ops : operators}.
  
  (* Formulas have falsity as fixed constant *)
  Inductive form : Type :=
  | atom : forall (P : preds), vec term (ar_preds P) -> form
  | bin : binop -> form -> form -> form
  | quant : quantop -> form -> form.
  
  Definition up (σ : nat -> term) := scons (var 0) (funcomp (subst_term (funcomp var S)) σ).

  Fixpoint subst_form (σ : nat -> term) (phi : form) : form :=
    match phi with
    | atom P v => atom P (map (subst_term σ) v)
    | bin op phi1 phi2 => bin op (subst_form σ phi1) (subst_form σ phi2)
    | quant op phi => quant op (subst_form (up σ) phi)
    end.

  Fixpoint depth_form (phi : form) : nat :=
      match phi with
      | atom P v => 0
      | bin op phi1 phi2 => S(depth_form phi1 + depth_form phi2)
      | quant op phi => S (depth_form phi)
      end.

End fix_signature.


Arguments term _, {_}.
Arguments var _ _, {_} _.
Arguments func _ _ _, {_} _ _.
Arguments subst_term {_} _ _.

Arguments form  _ _ _, _ _ {_}, {_ _ _}.
Arguments atom  _ _ _ _, _ _ {_ _}, {_ _ _ _}.
Arguments bin   _ _ _ _, _ _ {_ _}, {_ _ _ _}.
Arguments quant _ _ _ _, _ _ {_ _}, {_ _ _ _}.

Arguments up         _, {_}.
Arguments subst_form _ _ _, _ _ {_}, {_ _ _}.



(* Substitution Notation *)

Declare Scope subst_scope.
Open Scope subst_scope.

Notation "$ x" := (var x) (at level 3, format "$ '/' x") : subst_scope.
Notation "t `[ sigma ]" := (subst_term sigma t) (at level 7, left associativity, format "t '/' `[ sigma ]") : subst_scope.
Notation "phi [ sigma ]" := (subst_form sigma phi) (at level 7, left associativity, format "phi '/' [ sigma ]") : subst_scope.
Notation "s .: sigma" := (scons s sigma) (at level 70, right associativity) : subst_scope.
Notation "f >> g" := (funcomp g f) (at level 50) : subst_scope.
Notation "s '..'" := (scons s var) (at level 4, format "s ..") : subst_scope.
Notation "↑" := (S >> var) : subst_scope.


(* * Full Syntax *)

Declare Scope syn.
Open Scope syn.

Inductive full_logic_sym : Type :=
| Conj : full_logic_sym
| Disj : full_logic_sym
| Impl : full_logic_sym.

Inductive full_logic_quant : Type :=
| All : full_logic_quant
| Ex : full_logic_quant.

Definition full_operators : operators :=
  {| binop := full_logic_sym ; quantop := full_logic_quant |}.

#[export] Hint Immediate full_operators : typeclass_instances.


Notation "∀ Phi" := (@quant _ _ full_operators All Phi) (at level 50) : syn.
Notation "∃ Phi" := (@quant _ _ full_operators Ex Phi) (at level 50) : syn.
Notation "A ∧ B" := (@bin _ _ full_operators Conj A B) (at level 41) : syn.
Notation "A ∨ B" := (@bin _ _ full_operators Disj A B) (at level 42) : syn.
Notation "A '-->' B" := (@bin _ _ full_operators Impl A B) (at level 43, right associativity) : syn.
Notation "A '<-->' B" := ((A --> B) ∧ (B --> A)) (at level 43) : syn.





Require Import List.

Notation "x 'el' A" := (In x A) (at level 70).
Notation "A '<<=' B" := (incl A B) (at level 70).


Local Set Implicit Arguments.


Section ND_def.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Reserved Notation "A ⊢ phi" (at level 61).

  (* Definition of natural deduction for minimal logic *)

  Inductive prv : list form -> form -> Type :=
  | II A phi psi : phi::A ⊢ psi -> A ⊢ (phi --> psi)
  | IE A phi psi : A ⊢ phi --> psi -> A ⊢ phi -> A ⊢ psi
  | AllI A phi : map (subst_form ↑) A ⊢ phi -> A ⊢ ∀ phi
  | AllE A t phi : A ⊢ ∀ phi -> A ⊢ phi[t..]
  | ExI A t phi : A ⊢ phi[t..] -> A ⊢ ∃ phi
  | ExE A phi psi : A ⊢ ∃ phi -> phi::(map (subst_form ↑) A) ⊢ psi[↑] -> A ⊢ psi
  | Ctx A phi : phi el A -> A ⊢ phi
  | CI A phi psi : A ⊢ phi -> A ⊢ psi -> A ⊢ phi ∧ psi
  | CE1 A phi psi : A ⊢ phi ∧ psi -> A ⊢ phi
  | CE2 A phi psi : A ⊢ phi ∧ psi -> A ⊢ psi
  | DI1 A phi psi : A ⊢ phi -> A ⊢ phi ∨ psi
  | DI2 A phi psi : A ⊢ psi -> A ⊢ phi ∨ psi
  | DE A phi psi theta : A ⊢ phi ∨ psi -> phi::A ⊢ theta -> psi::A ⊢ theta -> A ⊢ theta
  where "A ⊢ phi" := (prv A phi).

End ND_def.


Arguments prv {_ _} _ _.
Notation "A ⊢M phi" := (prv A phi) (at level 55).


Section Minimal.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

(*  We formulate stability and explosiveness with respect to some fixed 
    closed formula ⊥ of our minimal logic. We can then show that if all 
    atomic formulas are explosive with respect to ⊥, then all formulas 
    are explosive with respect to ⊥. 
*)
  Variable falsity : form.
  Notation "⊥" := (falsity).
  Notation "¬ A" := (A --> ⊥) (at level 42) : syn.
  Hypothesis closed_bot : forall σ, ⊥[σ] = ⊥.

  (* Stability and Explosiveness with respect to ⊥ *)
  Definition stable ϕ := forall Γ, Γ ⊢M (((ϕ --> ⊥) --> ⊥) --> ϕ).
  Definition explosive ϕ := forall Γ, Γ ⊢M (⊥ --> ϕ).
  Definition stable_atoms := forall P t, stable (@atom _ _ _ P t).
  Definition explosive_atoms := forall P t, explosive (@atom _ _ _ P t).

  Fact stable_explosive ϕ :
    stable ϕ -> explosive ϕ.
  Proof.
    intros H Γ. apply II.
    eapply IE. apply H.
    apply II, Ctx; firstorder.
  Qed.

  Fact bot_el {ϕ Γ} :
    explosive ϕ -> ⊥ el Γ -> Γ ⊢M ϕ.
  Proof.
    intros Exp El.
    eapply IE with ⊥; [apply Exp| now apply Ctx].
  Qed.


  Lemma size_rect {X} σ f :
    (forall x, (forall y : X, σ y < σ x -> f y) -> f x) -> forall x, f x.
  Proof.
    intros H x. apply H.
    induction (σ x).
    - intros y. now intros F % PeanoNat.Nat.nlt_0_r.
    - intros y Hy. apply H.
      intros z Hz. apply IHn. lia.
  Defined.

  Fact depth_invar phi :
    forall sigma, depth_form(phi[sigma]) = depth_form phi.
  Proof.
    induction phi; cbn; congruence.
  Qed.

  Lemma Explosion :
    explosive_atoms -> forall ϕ, explosive ϕ.
  Proof.
    intros exp phi.
    pattern phi; revert phi.
    apply (size_rect depth_form).
    intros [| b phi1 phi2 | q phi ] Rec Γ; apply II.
    - apply bot_el; cbn; auto.
    - destruct b.
      + unshelve refine (
          let H := _ : _ in
          let sym phi e := H phi (Rec phi e) in
            CI (sym phi1 _) (sym phi2 _)
        ).
        2,3 : cbn; lia.
        intros A HA.
        refine (bot_el HA _); cbn; auto.
      + apply DI1.
        refine (bot_el (Rec _ _) _); cbn;[lia|auto].
      + apply II.
        refine (bot_el (Rec _ _) _); cbn;[lia|auto].
    - destruct q.
      + apply AllI.
        refine (bot_el (Rec _ _) _); cbn;[lia|auto].
      + eapply ExI with (t:= $0).
        refine (bot_el (Rec _ _) _); cbn;[|auto].
        rewrite depth_invar. lia.
  Qed.

  Lemma Explosion' :
    explosive_atoms -> forall ψ ϕ Γ, Γ ⊢M (¬ ψ --> ψ --> ϕ).
  Proof.
    intros exp psi phi Γ. apply II, II.
    eapply IE with ⊥. apply (Explosion exp).
    eapply IE with psi; apply Ctx; firstorder.
  Qed.


  Lemma drinker P x :
  let P_x := @atom _ _ _ P x in
    stable_atoms -> nil ⊢M ¬ ∀ ¬ (P_x --> ∀ P_x).
  Proof.
    cbn. intros stab.
    remember (atom x) as ϕ.
    apply II. eapply IE with ((ϕ --> ∀ ϕ)[$0..]).
    assert ( 
      (∀ ¬ (ϕ --> (∀ ϕ)) :: Datatypes.nil) ⊢M (¬ (ϕ --> (∀ ϕ)))[$0..]
    ) as H.
    - apply AllE, Ctx; now left.
    - admit.
    - cbn; apply II. apply AllI. cbn.
      subst. eapply IE. cbn.
  Admitted.

  
  Definition Perice_Transform phi := (⊥ --> phi) --> ⊥.
  Fixpoint PT (phi : form) :=
    match phi with
      | atom _ _ v => Perice_Transform (atom _ _ v)
      | bin _ _ _ Conj phi1 phi2 => (PT phi1) ∧ (PT phi2)
      | bin _ _ _ Disj phi1 phi2 => phi1 ∨ phi2
      | bin _ _ _ Impl phi1 phi2 => (PT phi1) --> (PT phi2)
      | quant _ _ _ Ex phi => ∃ phi
      | quant _ _ _ All phi => ∀ (PT phi)
      end.

  Variable PT_bot : PT ⊥ = ⊥.

  Lemma conservative Gamma phi : 
    Gamma ⊢M phi --> PT phi.
  Proof.
    induction phi; cbn; unfold Perice_Transform.
    - apply II, II.
  Admitted.


  Lemma idempotent Gamma ϕ :
    Gamma ⊢M PT (PT ϕ) --> PT ϕ.
  Proof.
    induction ϕ; cbn; unfold Perice_Transform.
    - apply II, II. rewrite PT_bot.
      eapply IE. apply Ctx; firstorder.
      apply II, II. apply Ctx; firstorder.
    - destruct b; cbn.
      + apply II. admit.
      + apply II, Ctx; firstorder.
      + 
  Admitted.





End Minimal.