Load Preamble.


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

  (* We use the stdlib definition of vectors to be maximally compatible  *)

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

  (* Syntax is parametrised in binary operators and quantifiers.
      Most developments will fix these types in the beginning and never change them.
   *)
  Class operators := {binop : Type ; quantop : Type}.
  Context {ops : operators}.
  
  (* Formulas have falsity as fixed constant -- we could parametrise against this in principle *)
  Inductive form : Type :=
  | falsity : form
  | atom : forall (P : preds), vec term (ar_preds P) -> form
  | bin : binop -> form -> form -> form
  | quant : quantop -> form -> form.
  
  Definition up (σ : nat -> term) := scons (var 0) (funcomp (subst_term (funcomp var S)) σ).

  Fixpoint subst_form (σ : nat -> term) (phi : form) : form :=
    match phi with
    | falsity => falsity
    | atom P v => atom P (map (subst_term σ) v)
    | bin op phi1 phi2 => bin op (subst_form σ phi1) (subst_form σ phi2)
    | quant op phi => quant op (subst_form (up σ) phi)
    end.

  Fixpoint depth_form (phi : form) : nat :=
    match phi with
    | falsity => 0
    | atom P v => 0
    | bin op phi1 phi2 => S(depth_form phi1 + depth_form phi2)
    | quant op phi => S (depth_form phi)
    end.


  (* Induction principle for terms *)

  Inductive Forall {A : Type} (P : A -> Type) : forall {n}, t A n -> Type :=
  | Forall_nil : Forall P (@Vector.nil A)
  | Forall_cons : forall n (x : A) (l : t A n), P x -> Forall P l -> Forall P (@Vector.cons A x n l).

  Inductive vec_in {A : Type} (a : A) : forall {n}, t A n -> Type :=
  | vec_inB {n} (v : t A n) : vec_in a (cons A a n v)
  | vec_inS a' {n} (v : t A n) : vec_in a v -> vec_in a (cons A a' n v).
  Hint Constructors vec_in : core.
  
  Lemma term_rect' (p : term -> Type) :
    (forall x, p (var x)) -> (forall F v, (Forall p v) -> p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2. fix strong_term_ind' 1. destruct t as [n|F v].
    - apply f1.
    - apply f2. induction v.
      + econstructor.
      + econstructor. now eapply strong_term_ind'. eauto.
  Qed.

  Lemma term_rect (p : term -> Type) :
    (forall x, p (var x)) -> (forall F v, (forall t, vec_in t v -> p t) -> p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2. eapply term_rect'.
    - apply f1.
    - intros. apply f2. intros t. induction 1; inversion X; subst; eauto.
      apply Eqdep_dec.inj_pair2_eq_dec in H2; subst; eauto. decide equality.
  Qed.

  Lemma term_ind (p : term -> Prop) :
    (forall x, p (var x)) -> (forall F v (IH : forall t, In t v -> p t), p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2. eapply term_rect'.
    - apply f1.
    - intros. apply f2. intros t. induction 1; inversion X; subst; eauto.
      apply Eqdep_dec.inj_pair2_eq_dec in H3; subst; eauto. decide equality.
  Qed.



End fix_signature.



(* Setting implicit arguments is crucial  *)
(* We can write term both with and without arguments, but printing is without. *)
Arguments term _, {_}.
Arguments var _ _, {_} _.
Arguments func _ _ _, {_} _ _.
Arguments subst_term {_} _ _.

(* Formulas can be written with the signatures explicit or not.
    If the operations are explicit, the signatures are too.
 *)
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



(* ** Substituion lemmas *)

Ltac cbns :=
    cbn; repeat (match goal with [ |- context f[subst_form ?sigma ?phi] ] => change (subst_form sigma phi) with (phi[sigma]) end).

Section Subst.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ops : operators}.

  Lemma subst_term_ext (t : term) sigma tau :
    (forall n, sigma n = tau n) -> t`[sigma] = t`[tau].
  Proof.
    intros H. induction t; cbn.
    - now apply H.
    - f_equal. now apply map_ext_in.
  Qed.

  Lemma subst_term_id (t : term) sigma :
    (forall n, sigma n = var n) -> t`[sigma] = t.
  Proof.
    intros H. induction t; cbn.
    - now apply H.
    - f_equal. now erewrite map_ext_in, map_id.
  Qed.

  Lemma subst_term_var (t : term) :
    t`[var] = t.
  Proof.
    now apply subst_term_id.
  Qed.

  Lemma subst_term_comp (t : term) sigma tau :
    t`[sigma]`[tau] = t`[sigma >> subst_term tau].
  Proof.
    induction t; cbn.
    - reflexivity.
    - f_equal. rewrite map_map. now apply map_ext_in.
  Qed.

  Lemma subst_term_shift (t : term) s :
    t`[↑]`[s..] = t.
  Proof.
    rewrite subst_term_comp. apply subst_term_id. now intros [|].
  Qed.

  Lemma up_term (t : term) xi :
    t`[↑]`[up xi] = t`[xi]`[↑].
  Proof.
    rewrite !subst_term_comp. apply subst_term_ext. reflexivity.
  Qed.

  Lemma up_ext sigma tau :
    (forall n, sigma n = tau n) -> forall n, up sigma n = up tau n.
  Proof.
    destruct n; cbn; trivial.
    unfold funcomp. now rewrite H.
  Qed.

  Lemma up_var sigma :
    (forall n, sigma n = var n) -> forall n, up sigma n = var n.
  Proof.
    destruct n; cbn; trivial.
    unfold funcomp. now rewrite H.
  Qed.


  Lemma up_funcomp sigma tau :
    forall n, (up sigma >> subst_term (up tau)) n = up (sigma >> subst_term tau) n.
  Proof.
    intros [|]; cbn; trivial.
    setoid_rewrite subst_term_comp.
    apply subst_term_ext. now intros [|].
  Qed.

  Lemma subst_ext (phi : form) (sigma tau : nat -> term) :
    (forall n, sigma n = tau n) -> phi[sigma] = phi[tau].
  Proof.
    induction phi in sigma, tau |- *; cbns; intros H.
    - reflexivity.
    - f_equal. apply map_ext. intros s. now apply subst_term_ext.
    - now erewrite IHphi1, IHphi2.
    - erewrite IHphi; trivial. now apply up_ext.
  Qed.

  Lemma subst_id (phi : form) sigma :
    (forall n, sigma n = var n) -> phi[sigma] = phi.
  Proof.
    induction phi in sigma |- *; cbns; intros H.
    - reflexivity.
    - f_equal. erewrite map_ext; try apply map_id. intros s. now apply subst_term_id.
    - now erewrite IHphi1, IHphi2.
    - erewrite IHphi; trivial. now apply up_var.
  Qed.

  Lemma subst_var (phi : form) :
    phi[var] = phi.
  Proof.
    now apply subst_id.
  Qed.

  Lemma subst_comp (phi : form) sigma tau :
    phi[sigma][tau] = phi[sigma >> subst_term tau].
  Proof.
    induction phi in sigma, tau |- *; cbns.
    - reflexivity.
    - f_equal. rewrite map_map. apply map_ext. intros s. apply subst_term_comp.
    - now rewrite IHphi1, IHphi2.
    - rewrite IHphi. f_equal. now apply subst_ext, up_funcomp.
  Qed.

  Lemma subst_shift (phi : form) s :
    phi[↑][s..] = phi.
  Proof.
    rewrite subst_comp. apply subst_id. now intros [|].
  Qed.

  Lemma up_form xi psi :
    psi[↑][up xi] = psi[xi][↑].
  Proof.
    rewrite !subst_comp. apply subst_ext. reflexivity.
  Qed.

  Fixpoint iter {X: Type} f n (x : X) :=
    match n with
      0 => x
    | S m => f (iter f m x)
    end.

  Lemma iter_switch {X} f n (x : X) :
    f (iter f n x) = iter f n (f x).
  Proof.
    induction n. reflexivity.
    cbn. now rewrite IHn.
  Qed.

  Lemma up_decompose sigma phi : phi[up (S >> sigma)][(sigma 0)..] = phi[sigma].
  Proof.
    rewrite subst_comp. apply subst_ext.
    intros [].
    - reflexivity.
    - apply subst_term_shift.
  Qed.

  Lemma depth_invar phi : 
    forall sigma, depth_form(phi[sigma]) = depth_form phi.
  Proof.
    induction phi; cbn; try congruence. 
  Qed.



End Subst.




(* Local Set Implicit Arguments.
Local Unset Strict Implicit.
 *)

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
Notation "⊥" := (falsity) : syn.
Notation "¬ A" := (A --> ⊥) (at level 42) : syn.
Notation "A '<-->' B" := ((A --> B) ∧ (B --> A)) (at level 43) : syn.





Require Import List.

Notation "x 'el' A" := (In x A) (at level 70).
Notation "A '<<=' B" := (incl A B) (at level 70).


Local Set Implicit Arguments.

(* Tag for different flavors of first-order logic *)
Inductive flavor := class | intu | peirce | min.
Existing Class flavor.

Section ND_def.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Reserved Notation "A ⊢ phi" (at level 61).
  
  (* * Definition *)

  Implicit Type fl : flavor.

  Inductive prv : forall fl, list form -> form -> Type :=
  | II {fl} A phi psi : phi::A ⊢ psi -> A ⊢ (phi --> psi)
  | IE {fl} A phi psi : A ⊢ phi --> psi -> A ⊢ phi -> A ⊢ psi
  | AllI {fl} A phi : map (subst_form ↑) A ⊢ phi -> A ⊢ ∀ phi
  | AllE {fl} A t phi : A ⊢ ∀ phi -> A ⊢ phi[t..]
  | ExI {fl} A t phi : A ⊢ phi[t..] -> A ⊢ ∃ phi
  | ExE {fl} A phi psi : A ⊢ ∃ phi -> phi::(map (subst_form ↑) A) ⊢ psi[↑] -> A ⊢ psi
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


Arguments prv {_ _ _} _ _.
Notation "A ⊢ phi" := (prv A phi) (at level 55).
Notation "A ⊢C phi" := (@prv _ _ class A phi) (at level 55).
Notation "A ⊢I phi" := (@prv _ _ intu A phi) (at level 55).
Notation "A ⊢M phi" := (@prv _ _ min A phi) (at level 55).
Notation "A ⊢P phi" := (@prv _ _ peirce A phi) (at level 55).


Ltac comp := repeat (progress (cbn in *; autounfold in *)).
Hint Constructors prv : core.


Section ND_def.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Context {fl : flavor}.

  Theorem Weak A B phi :
    A ⊢ phi -> A <<= B -> B ⊢ phi.
  Proof.
    intros H. revert B.
    induction H; intros B HB; try unshelve (solve [econstructor; intuition]); try now econstructor.
  Qed.


  Lemma combine_context {Γ1 Γ2} alpha beta : Γ1 ⊢ alpha -> Γ2 ⊢ (alpha --> beta) -> (Γ1 ++ Γ2) ⊢ beta.
  Proof.
    intros H1 H2.
    apply (@Weak _ (Γ1 ++ Γ2)) in H1.
    apply (@Weak _ (Γ1 ++ Γ2)) in H2.
    eapply IE; eassumption.
    now apply incl_appr. now apply incl_appl.
  Qed.

  Lemma imps T phi psi :
    T ⊢ phi --> psi <=> (phi :: T) ⊢ psi.
  Proof.
    split; try apply II.
    intros H. apply IE with phi; auto. apply (Weak H). firstorder.
    apply Ctx. firstorder.
  Qed.

  Lemma CE T phi psi :
    T ⊢ phi ∧ psi -> prod (T ⊢ phi) (T ⊢ psi).
  Proof.
    intros H. split.
    - apply (CE1 H).
    - apply (CE2 H).
  Qed.

  Lemma DE' A phi :
    A ⊢ phi ∨ phi -> A ⊢ phi.
  Proof.
    intros H. apply (DE H); apply Ctx; firstorder.
  Qed.

  Lemma switch_conj_imp alpha beta phi A :
    A ⊢ alpha ∧ beta --> phi <=> A ⊢ alpha --> beta --> phi.
  Proof.
    split; intros H.
    - apply II, II. eapply IE.
      apply (@Weak A). apply H. firstorder.
      apply CI; apply Ctx; firstorder.
    - apply II. eapply IE. eapply IE.
      eapply Weak. apply H.
      firstorder.
      eapply CE1, Ctx; firstorder.
      eapply CE2, Ctx; firstorder.
  Qed.


End ND_def.


Section Minimal.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Hypothesis (DNE_atom : 
    forall P t A, A ⊢M (((@atom _ _ _ P t --> ⊥) --> ⊥) --> @atom _ _ _ P t)).

  Lemma size_rect {X} σ f : 
    (forall x, (forall y : X, σ y < σ x -> f y) -> f x) -> forall x, f x.
  Proof.
    intros H x. apply H.
    induction (σ x).
    - intros y. now intros F % PeanoNat.Nat.nlt_0_r. 
    - intros y Hy. apply H.
      intros z Hz. apply IHn. lia.
  Defined.

  Lemma Explosion phi :
    forall A Γ, Γ ⊢M (A --> ⊥) --> A --> phi.
  Proof.
    pattern phi; revert phi.
    refine (size_rect depth_form _ _).
    intros phi Rec A Γ.
    destruct phi.
    2-4: apply II, II.
    - apply II, Ctx. now left.
    - eapply IE. apply DNE_atom.
      apply II. eapply IE.
      all: apply Ctx; right; firstorder.
    - destruct b.
      + apply CI.
        * eapply IE. eapply IE. apply Rec; cbn; lia.
          all: apply Ctx; firstorder.
        * eapply IE. eapply IE. apply Rec; cbn; lia.
        all: apply Ctx; firstorder.
      + apply DI1. eapply IE. eapply IE. apply Rec; cbn; lia.
        all: apply Ctx; firstorder.
      + apply II. eapply IE. eapply IE. apply Rec; cbn; lia.
        all: apply Ctx; firstorder.
    - destruct q.
      + apply AllI. cbn.
        eapply IE. eapply IE. apply Rec; cbn; lia.
        all: apply Ctx; firstorder.
      + eapply ExI with (t:= $0).
        eapply IE. eapply IE. apply Rec.
        rewrite depth_invar. cbn; lia.
        all: apply Ctx; firstorder.
  Qed.

End Minimal.


Section Minimal.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Lemma Transform Γ ϕ :
    forall (proof : Γ ⊢C ϕ), { tΓ &{ tϕ & Γ ⊢C ϕ <=> tΓ ⊢I tϕ }}.
  Proof.
    intros proof. induction proof.
    - destruct IHproof as (tΓ & tϕ & ?).
      exists tΓ, tϕ. split.
      + intros ?. now apply i.
      + intros ?%i. now apply II.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - 


End Minimal.