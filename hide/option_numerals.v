Require Import Lia.

Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.
Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
Notation p1 := projT1.

Definition dec (P : Type) := (P + (P -> False))%type. 
Definition EQ X := forall x y : X, dec (x = y).

Definition surj {X Y} (f : X -> Y) := forall y, exists x, f x = y.
Definition inj {X Y} (f : X -> Y) := forall x x', f x = f x' -> x = x'.
Definition inv {X Y} (g: Y -> X) (f: X -> Y) := forall x, g (f x) = x.

Inductive Bij (X Y : Type) : Type :=
| Bijection: forall (f: X -> Y) (g: Y -> X), inv f g -> inv g f -> Bij X Y.
Arguments Bijection {X Y}.


Fact inv_inj {X Y} (f : X -> Y) g : 
  inv g f -> inj f.
Proof.
  intros gf x y E. now rewrite <-(gf x), <-(gf y), E.
Qed.

Lemma dec_None {X} : forall x : option X, dec(x = None).
Proof.
  intros [|]; [right|left]; congruence.
Qed.

Fact EQ_option X : EQ X -> EQ (option X).
Proof.
  intros eq_dec [x|] [y|]; [|right|right|left]; try congruence.
  destruct (eq_dec x y); [left|right]; congruence.
Qed.


Definition rw {X Y} (f : option X -> option Y) ox :=
  match ox with
  | None => None
  | Some x => match f (Some x) with
              | Some y => Some y
              | None => f None
  end end.

Definition RW {X Y} f (x : X) (y : Y) :=
  match f (Some x) with 
  | Some y' => y = y' 
  | None => f None = Some y
  end.

Fact rw_RW {X Y} (f : option X -> option Y) :
forall x y, (rw f) (Some x) = Some y <-> RW f x y.
Proof.
  intros x y. unfold rw, RW.
  destruct (f (Some x)); split; congruence.
Qed.


Definition rw_elim {X Y} (f : option X -> option Y) (g : option Y -> Type) :
  g None ->
  (forall x y, f (Some x) = Some y -> g (Some y)) ->
  (forall x y, f (Some x) = None -> f None = Some y -> g (Some y)) ->
  forall x, g (rw f x).
Proof.
  intros H0 H1 H2 [x|]; unfold rw.
  - destruct (f (Some x)) eqn:?.
    + now apply (H1 x).
    + destruct (f None) eqn:?; [|auto].
      now apply (H2 x).
  - assumption.
Qed.


Fact rw_spec1 {X Y} (f : option X -> option Y) :
  forall x y, f (Some x) = Some y -> rw f (Some x) = Some y.
Proof.
  unfold rw. now intros ?? ->.
Qed.

Fact rw_spec2 {X Y} (f : option X -> option Y) :
  forall x, x <> None -> f x <> None -> rw f x = f x.
Proof.
  intros [x|] H1 H2; [|tauto].
  unfold rw. destruct (f (Some x)).
  - reflexivity.
  - congruence.
Qed.


Lemma rw_invar' {X Y} (f : option X -> option Y) :
  f None = None <-> (forall x, rw f x = f x).
Proof.
  split; intros H.
  - intros [x|]; unfold rw.
    destruct (f (Some x)).
    all: congruence.
  - symmetry. apply (H None).
Qed.

Lemma rw_invar {X Y} (f : option X -> option Y) x :
  f None = None -> rw f x = f x.
Proof.
  intros H. now apply rw_invar'.
Qed.


Lemma inv_inv_rw {X Y} (f : option X -> option Y) g :
  inv g f -> inv (rw g) (rw f).
Proof.
  intros gf [x|]; [|reflexivity].
  unfold rw. destruct (f (Some x)) as [y|] eqn:E.
  * now rewrite <-E, gf.
  * destruct (f None) eqn:E'.
    rewrite <-E', gf.
    all: congruence.
Qed.


(* We cannot leave out the first two conditions. There are counterexamples such that the conclusion then no longer works. *)
Lemma inv_rw_inv {X Y} (f : option X -> option Y) g :
   g (f None) = None -> f (g None) = None ->
   inv (rw g) (rw f) -> inv g f.
Proof.
  intros gf0 fg0 Inv [x|]; [|assumption].
  generalize (Inv (Some x)).
  destruct (f None) eqn:Hf.
  2 : { now rewrite !rw_invar. }
  destruct (g None) eqn:Hg.
  all: unfold rw; destruct (f (Some x)) as [y'|] eqn:?.
  * destruct (g (Some y')) eqn:E2; congruence.
  * now rewrite Hf, gf0.
  * now rewrite <-rw_invar at 2.
  * now rewrite Hf, gf0, Hg.
Qed.



Lemma pRewire3 {X Y} (f : option X -> option Y) g :
  (f None = None /\ g None = None) ->
  (inv g f) <=>
  (forall x, Sigma y, f (Some x) = Some y 
                  /\ g (Some y) = Some x).
Proof.
  intros []. split.
  - intros gf x; destruct (f (Some x)) as [y|] eqn:E.
    + exists y. split; congruence.
    + congruence.
  - intros h [x|].
    + destruct (h x) as [y []]. congruence.
    + congruence.
Qed.



(* Lemma pRewire3 {X Y} (f : option X -> option Y) g :
  prod (f None = None) (inv g f) <=>
  prod (f None = None /\ g None = None)
  (forall x, Sigma y, f (Some x) = Some y 
                  /\ g (Some y) = Some x).
Proof.
  split.
  - intros [? gf]; split.
    { split; congruence. }
    intros x; destruct (f (Some x)) as [y|] eqn:E.
    + exists y. split; congruence.
    + congruence.
  - intros [[] h]; split.
    { congruence. }
    intros [x|].
    + destruct (h x) as [y []]. congruence.
    + congruence.
Qed.
 *)

Lemma pRewire4 {X Y} (f : option X -> option Y) x :
  ~ (f None = None /\ f (Some x) = None) <=>
  Sigma y, rw f (Some x) = Some y.
Proof.
  unfold rw; destruct (f (Some x)) as [y|] eqn:E.
  - split; intros _; [now exists y|].
    intros []. discriminate.
  - split.
    + intro. destruct (f None); [eauto|tauto].
    + intros [][]; congruence.
Qed.


Lemma pRewire'' {X Y} (f : option X -> option Y) :
  (forall x, rw f x = None -> x = None) <=>
  forall x, Sigma y, rw f (Some x) = Some y.
Proof.
  split.
  - intros H x. apply pRewire4. intros [? E].
    generalize (H (Some x)). unfold rw.
    rewrite E. intuition discriminate.
  - intros H [x|].
    + destruct (H x). congruence.
    + auto.
Qed.



Lemma pRewire4'' {X Y} (f : option X -> option Y) x :
  (f None = None /\ f x = None -> x = None) <=>
  Sigma y, rw f x = Some y.
Proof.
  split.
  - intros H. destruct x as [x|]; unfold rw.
    destruct (f (Some x)) as [y|].
    + now exists y.
    + destruct (f None) as [y|].
      * now exists y.
      * intuition discriminate.
    + admit.
  - intros [y Hy] [? H]; unfold rw in *.
    destruct x as [x|].
    + rewrite H in Hy. congruence.
    + reflexivity.
Admitted.


Lemma pRewire2 {X Y} (f : option X -> option Y) g :
  inv (rw g) (rw f) <=>
  forall x, Sigma y, rw f (Some x) = Some y 
                  /\ rw g (Some y) = Some x.
Proof.
  now apply pRewire3.
Qed.


Lemma pRewire1 {X Y} (f : option X -> option Y) :
  f None = None ->
  (inj f) <=>
  forall x, Sigma y, f (Some x) = Some y
      /\ forall x', f (Some x') = Some y -> x' = x.
Proof.
  intros none. split.
  - intros inj_f x; destruct (f (Some x)) as [y|] eqn:E.
    + exists y. split; trivial.
      intros x'. rewrite <-E.
      now intros [=] % inj_f.
    + rewrite <-none in E.
      now apply inj_f in E.
  - intros H [x|] ox E.
    + destruct (H x) as [y [H1 H2]].
      destruct ox.
      * f_equal. symmetry. apply H2. congruence.
      * congruence.
    + destruct ox as [x|]; auto.
      destruct (H x) as [? []]. congruence.
Qed.


(* The more general lemma to Rewire. *)
Lemma pRewire {X Y} (f : option X -> option Y) :
  (forall x, f x = None -> x = None) <=>
  forall x, Sigma y, f (Some x) = Some y.
Proof.
  split.
  - intros H x; destruct (f (Some x)) as [y|] eqn:E.
    + now exists y.
    + now apply H in E.
  - intros h [x|].
    + destruct (h x). congruence.
    + congruence.
Qed.

Definition map {X Y} (f : X -> Y) ox := 
  match ox with
  | None => None
  | Some x => Some (f x)
  end.

Lemma new {X Y} (f : option X -> option Y) :
  (forall x, f x = None -> x = None) * (f None = None) <=>
  Sigma F, forall ox , f ox = (map F) ox .
Proof.
  split.
  * intros [H f0]. specialize (fst (pRewire f) H) as F.
    exists (fun x => p1 (F x)).
    intros [x|].
    - cbn; now destruct (F x).
    - assumption.
  * intros [F HF]. split.
    - intros [x|]; auto.
      specialize (HF (Some x)).
      cbn in *. congruence.
    - apply HF.
Qed.


Lemma new' {X Y} (f : option X -> option Y) :
  f None <> None ->
  Sigma F, forall ox ,
    rw f ox = match ox with 
            None => None | Some x => Some (F x) end.
Proof.
  intros f0.
  assert (H : forall x, rw f x = None -> x = None).
  { intros [x|]; unfold rw; [|tauto].
    destruct (f (Some x)); congruence. }
  specialize (fst (pRewire _) H) as F.
    exists (fun x => p1 (F x)).
    intros [x|].
    - now destruct (F x).
    - now unfold rw. 
Qed.



Lemma Rewire {X Y f g} (gf : inv g f) :
  forall x : X, Sigma y : Y, (rw f) (Some x) = Some y.
Proof.
  apply pRewire. unfold rw.
  intros [x|] H; [|reflexivity].
  destruct (f (Some x)) eqn:?; congruence.

  Restart.
  intros x; unfold rw.
  destruct (f (Some x)) as [y|] eqn:?.
  - now exists y.
  - destruct (f None) as [y|] eqn:?.
    + now exists y.
    + exfalso. congruence. 
Qed.

Definition R {X Y g f} gf := fun x => p1 (@Rewire X Y f g gf x).





Lemma Rewire_inv {X Y} (f : option X -> option Y) g :
  forall (f_ : inv f g) (g_ : inv g f),
    inv (R f_) (R g_).
Proof.
  intros f_ g_ x. unfold R.
  destruct (Rewire g_ x) as [y ]; cbn.
  destruct (Rewire f_ y) as []; cbn.
  unfold rw in *.
  destruct  (f (Some x)) as [|] eqn:?,
            (g (Some y)) as [|] eqn:?; congruence.
Qed.

Lemma Bij_option X Y :
  Bij (option X) (option Y) -> Bij X Y.
Proof.
  intros [].
  eexists; apply Rewire_inv.
  Unshelve. all: eassumption.
Qed.


(* Some notes regarding the old Rewireing: *)


Lemma equiv' X Y (f : option X -> option Y) :
  forall x y, 
  ( (forall z, f (Some x) = Some z -> z = y) 
  /\ (f (Some x) = None -> f None = Some y)) <->
  (rw f) (Some x) = Some y.
Proof.
  intros x y. unfold rw.
  destruct (f (Some x)); split; try intuition congruence.
  intros []. f_equal. now apply H.
Qed.



Lemma old_Rewire_equiv {X Y} (f : option X -> option Y) :
  (f None = None -> forall x, exists y, f (Some x) = Some y) <=>
  forall x, Sigma y, RW f x y.
Proof.
  split; unfold RW.
  - intros H x.
    destruct (f (Some x)) as [y|] eqn:?.
    + now exists y.
    + destruct (f None) as [y|] eqn:?.
      * now exists y.
      * exfalso. destruct (H eq_refl x).
        congruence.
  - intros F f_none x.
    destruct (F x), (f (Some x)) as [z|] eqn:?.
    + now exists z.
    + congruence.
Qed.

(* Where we additionally have the equivalence *)
Goal forall X Y (f : option X -> option Y),
  (forall x, exists y, f (Some x) = Some y) <->
  forall x, f x = None -> x = None.
Proof.
  split; intros H.
  - intros [x|] E.
    + destruct (H x). congruence.
    + reflexivity.
  - intros x. destruct (f (Some x)) as [y|] eqn:E.
    + now exists y.
    + exfalso. apply H in E. discriminate.
Qed.



(* Define finite types with n elements *)
Fixpoint Num (n : nat) : Type :=
  match n with 
  | 0 => False 
  | S n => option (Num n) 
  end.

Definition elim_Num (f : forall n (a : Num n), Type) :
  (forall n, f (S n) None) ->
  (forall n a, f n a -> f (S n) (Some a)) ->
  (forall n a, f n a).
induction n; intros []; auto.
Defined.


Lemma Bij_Num n :
  forall m, Bij (Num n) (Num m) -> n = m.
Proof.
  induction n as [|n IHn]; intros [|m]; auto.
  1, 2: intros [f g ]; exfalso.
  - exact (g None).
  - exact (f None).
  - cbn. intros ?%Bij_option%IHn.
    now f_equal.
Qed.


Fact EQ_Num n : EQ (Num n).
Proof.
  induction n as [|n IH].
  - intros [].
  - cbn. now apply EQ_option.
Qed.


Definition num2nat : forall n, Num n -> nat.
  intros n.
  induction n as [|n rec].
  - intros [].
  - intros [x|].
    + exact (S (rec x)).
    + exact 0.
Defined.


Lemma inv_comm n (f g : Num n -> Num n) :
  inv g f -> inv f g.
Proof.
  induction n; intros gf.
  1: intros [].
  specialize (inv_inv_rw _ _ gf) as H.
  specialize (fst (pRewire2 f g) H) as F; fold Num in *.
  
Admitted.


Lemma surj_surj n (f : Num (S n) -> Num (S n)) :
  surj f <-> surj (rw f).
Proof.
  specialize (EQ_Num (S n)) as eq.
  split; intros H; unfold surj; fold Num.
  - destruct (f None) eqn:?.
    2 : { intros y. destruct (H y) as [x Hx].
          exists x. now rewrite rw_invar. }  
    intros [y|].
    2: now exists None.
    destruct (eq (f None) (Some y)) as [E|E].
    + destruct (H None) as [[x0|] H0].
      exists (Some x0). unfold rw. now rewrite H0.
      enough (Some y = None) by congruence.
      now rewrite <-E.
    + destruct (H (Some y)) as [[x|] Hx]. 2: tauto.
      exists (Some x). unfold rw. now rewrite Hx.
  - admit.
Admitted.


(* Group approach *)

Definition eq_fext {X Y} (f g : X -> Y) := forall x, f x = g x.
Definition comp {X Y Z} (g : Y -> Z) f := fun x : X => g (f x).
Definition id {X} := fun x : X => x.
Infix "==" := eq_fext (at level 30).
Infix "<<" := comp (at level 20).


Goal forall X Y f g, @inv X Y f g <-> (f << g) == id.
Proof.
  intros X Y f g. unfold "==", "<<".
  intuition.
Qed.

(* Highly non true *)
Lemma Num_left_inv n (f : Num n -> Num n) :
  Sigma g, (g << f) == id.
Proof.
Admitted.


Lemma idemp n (f g : Num n -> Num n) :
  inv g f -> (f << g) << (f << g) == f << g.
Proof.
  intros H x. unfold "<<". congruence.
Qed.

Lemma Num_lr_inv n (f g : Num n -> Num n) :
  inv g f -> inv f g.
Proof.
  intros H.
Admitted.  

Lemma Num_eq_inv n (f g h : Num n -> Num n) :
  inv g f -> inv f h -> g == h.
Proof.
  intros. cut (g == g << (f << h)).
  all : intros x; unfold "<<"; congruence.
Qed.