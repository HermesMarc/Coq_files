Require Import Coq.Lists.List.
Require Import Lia.
Set Implicit Arguments.

Structure Group :=
{ X:>Type ; m : X -> X -> X ; e : X ; i : X -> X ;
Neutral : forall x, m x e = x  ;
Inverse : forall x, m x (i x) = e ;
Asso : forall x y z, m x (m y z) = m (m x y ) z
}.

Arguments m {_} _ _.
Arguments e {_}.
Arguments i {_} _.
Arguments Neutral {_} _.
Arguments Inverse {_} _.

Notation "x # y" := (m x y) (at level 50).

Structure abelianGroup :=
{ G:> Group ; Com : forall x y : G, x # y = y # x }.



(* Basic Facts *)

(* astonishingly useful and easy to show *)
Lemma neutral_idempotent : forall G : Group, forall x : G, x # x = x -> x = e.
Proof.
  intros G x eq. rewrite <- (Neutral x). rewrite <- (Inverse x). 
  rewrite Asso. rewrite eq. reflexivity.
Qed.


Theorem right_intro {G : Group} : forall a b x: G, a = b <-> a # x = b # x.
Proof.
  intros a b x. split; intros eq.
  - pattern x. rewrite eq. reflexivity. 
  - rewrite <- Neutral. rewrite <-(Inverse x). rewrite Asso.
    rewrite <- eq. rewrite <- Asso. rewrite Inverse. rewrite Neutral; trivial.
Qed.


Theorem neutral_unique : forall (G : Group) (y : G), (forall x, x # y = x) -> y = e.
Proof.
  intros G y H. specialize (H y). apply neutral_idempotent in H. exact H.
Qed.


Lemma left_inverse : forall (G : Group) (x : G), (i x) # x = e.
Proof.
  intros G x. apply neutral_idempotent. rewrite <- Asso. pattern (x # (i x # x)).
  rewrite Asso, Asso. rewrite Inverse. rewrite Neutral. reflexivity.
Qed.


Lemma left_neutral : forall (G : Group) (x : G), e # x = x.
Proof.
  intros G x. rewrite <- (Inverse x). rewrite <- Asso. pattern (i x # x). 
  rewrite left_inverse. apply Neutral. 
Qed.


Theorem left_intro {G : Group}: forall a b x: G, a = b <-> x # a = x # b.
Proof. 
  intros a b x. split; intro eq.
  - pattern x. rewrite eq. reflexivity.
  - rewrite <- (left_neutral G a). rewrite <- (left_inverse G x). rewrite <- Asso.
    rewrite eq. rewrite Asso. rewrite left_inverse. rewrite left_neutral; trivial.
Qed.


Lemma i_idempotent : forall G : Group, forall x : G, i (i x) = x.
Proof.
  intros G x. pattern x at 2. rewrite <- (Neutral x). rewrite <- (Inverse (i x)).
  rewrite Asso. rewrite Inverse. rewrite left_neutral. trivial.
Qed.
  

Theorem i_product : forall G : Group, forall x y: G, i (x # y) = (i y) # (i x).
Proof.
  intros G x y. apply (right_intro _ _ (x # y) ). rewrite left_inverse.
  rewrite <- Asso. pattern (i y). rewrite Asso. rewrite left_inverse.
  rewrite Asso. rewrite Neutral. rewrite left_inverse; trivial.
Qed.



(* Morphisms *)

Definition comp {X1 X2 X3 : Type}(phi23 : X2 -> X3) (phi12 : X1 -> X2) : X1 -> X3 :=
  fun x : X1 => phi23 (phi12 x).


Definition inj {A B : Type} (f : A -> B) : Prop :=
  forall x y, f x = f y -> x = y.

Definition surj {A B : Type} (f : A -> B) : Prop :=
  forall y, exists x, f x = y.

Definition bij {A B : Type} (f : A -> B) : Prop :=
  inj f /\ surj f. 



Definition hom {G H : Group}(phi : G -> H) : Prop :=
  forall x y : G,  phi(x # y) = (phi x) # (phi y).

Definition Hom (G H : Group) := {phi : G -> H | hom phi }.

Notation "p .1" := (proj1_sig p) (at level 2).
Notation "p .2" := (proj2_sig p) (at level 2).

Definition iso {G H : Group}(phi : Hom G H) : Prop := bij (phi.1).

Definition subgroup {G H : Group}(phi : Hom G H) : Prop := inj (phi.1).



Lemma hom_composition {G1 G2 G3 : Group}(phi1 : Hom G1 G2) (phi2 : Hom G2 G3 ) :
  hom (comp (phi2.1) (phi1.1)).
Proof.
  intros x y. unfold comp. 
  destruct phi1 as [phi1 H1]. destruct phi2 as [phi2 H2]. 
  rewrite <- H2. rewrite <- H1. trivial.
Qed.


Lemma hom_e {G H: Group} (phi : Hom G H) : (phi.1) e = e.
Proof.
  destruct phi as [phi Hom]. assert (phi e # phi e = phi e).
  change ( (fun x => phi e # phi e = phi x ) e ). rewrite <- Neutral. rewrite Hom. auto.
  cbn. apply neutral_idempotent in H0. auto.
Qed.


Lemma hom_i {G H: Group} (phi : Hom G H) : 
  forall x, (phi.1) (i x) = i ((phi.1) x).
Proof.
  intros x. destruct phi as [phi Hom]. cbn.
  apply (left_intro _ _ (phi  x) ). rewrite <- Hom.
  rewrite Inverse, Inverse. 
  change ( (exist (fun phi0 : G -> H => hom phi0) phi Hom).1 e = e).
  apply hom_e.
Qed.



(* Zero object in the theory of groups *)

Definition unique {G H : Group} (phi : Hom G H) := forall psi : Hom G H, psi.1 = phi.1 . 

Definition initial (G : Group) := forall H : Group, exists phi : Hom G H,
  unique phi .

Definition terminal (G : Group) := forall H : Group, exists phi : Hom H G,
  unique phi .


Axiom ZeroObj : exists G : Group, initial G /\ terminal G.

(* To validate the Axiom, we should define the trivial Group *)




(* More on morphisms *)

Definition prekernel {X Y K : Group}(phi : Hom X Y)(k : Hom K X) : Prop :=
  forall x : K, (phi.1) ((k.1) x) = e.

Definition kernel {X Y K : Group}(phi : Hom X Y)(k : Hom K X) : Prop :=
  prekernel phi k /\ 
  forall (K' :Group)(k' : Hom K' X), prekernel phi k' 
                             -> exists (i : K' -> K), comp (k.1) i = (k'.1).



Theorem kernel_subgroup : forall (H G K: Group)(phi : Hom H G)(k : Hom K H), 
  kernel phi k -> subgroup k.
Proof.
  intros H G K phi k ker. unfold subgroup.
  intros x y eq. apply (right_intro _ _ (i y)). rewrite Inverse.
Admitted.


Definition image {G H : Group} (phi : Hom G H) := 
  { h : H | exists g : G, (phi .1) g = h }.


Definition normal {G N : Group}(phi : Hom N G) :=
  subgroup phi -> forall (n : N)(g : G), exists (n' :N), g # ((phi.1) n) = ((phi.1) n') # g. 



Definition trivial (G : Group) := forall g : G, g = e.

Axiom trivialGroup : exists G : Group, trivial G.

Goal forall (G H K: Group)(phi : Hom G H)(k : Hom K G),
  kernel phi k -> normal k.
Proof.
  intros G H K phi k Ker. intros Sub n g.
  destruct Ker as [preker I]. destruct trivialGroup as [E triv].
Admitted.




(* Quotient Groups *)

Definition prekernel {X Y K : Group}(phi : Hom X Y)(k : Hom K X) : Prop :=
  forall x : K, (phi.1) ((k.1) x) = e.

Definition prequotient {X Y Q: Group} 



Theorem Isomorphism {G H : Group}(phi : Hom G H) : True.
Abort.






(* General associativity of group expressions *)

Inductive gexp : Type :=
  E : gexp
| var : nat -> gexp
| inv : gexp -> gexp
| mult : gexp -> gexp -> gexp.


Fixpoint eval {G : Group} (rho : nat -> G) (t : gexp) : G :=
  match t with
  | E => e
  | var n => rho n
  | inv a => i (eval rho a)
  | mult a b => (eval rho a) # (eval rho b)
  end.


(* Makes a list of all elements in the expression, in the order they appear *)
Fixpoint gexpList (t : gexp) : list gexp :=
  match t with
  | mult a b => gexpList a ++ gexpList b
  | s => cons s nil
  end.

Fixpoint iter {X:Type} (n: nat)(f : X -> X)(x : X) : X :=
  match n with
  | 0 => x
  | S m => f (iter m f x)
  end.




Lemma fixpoint {X:Type}(f : X -> X)(x : X)(s : X -> nat) :
  ( forall n, s (iter n f x) > s (iter (S n) f x) \/ iter n f x = x )
                          -> iter (s x) f x = x.
Proof.
  intro H. assert (forall m, S (s x) > m + s(iter m f x) \/ iter m f x = x).
  intro m. induction m.
  - cbn; firstorder.
  - destruct IHm as [A | B]. destruct (H m0) as [A' | B'].
    replace (S m0 + s (iter (S m0) f x)) with (S (m0 + s (iter (S m0) f x))) by lia.
  + lia.
  + right. cbn. rewrite B'. change (iter 1 f x = x). 
Abort.

Fixpoint elements (T :gexp) : nat :=
  match T with
  | mult a b => (elements a) + (elements b)
  | s => 1
  end.


Fixpoint norm' (T :gexp)(n :nat) : gexp :=
  match T, n with
  | t, 0 => t
  | mult t0 t3, S n => match t0 with 
                  | mult t1 t2 => norm' ( mult t1 (mult t2 t3) ) n
                  | s => mult s ( norm' t3 n )
                  end
  | t, _ => t
  end.



Definition strongInduction := forall (p : nat -> Prop),
  (forall n, (forall k, k < n -> p k) -> p n) -> (forall n, p n).

Definition Induction := forall (p : nat -> Prop),
  p 0 -> (forall n, p n -> p (S n)) -> (forall n, p n).

Goal Induction.
Proof.  intros p p0 IH. induction n; auto. Qed.

Goal Induction -> strongInduction.
Proof.
  intros ind p SI n.
  pose (Q n := forall k, k < n -> p k).
  assert (Q (S n) -> p n). unfold Q. intro H. apply H. lia.
  apply H. apply ind. unfold Q. intro k; lia.
  intros m Hm. assert (Q m /\ p m -> Q (S m)) as F.
  { intros [Qm Pm]. unfold Q. intros k.
  assert ( (k < S m) <-> ( k < m \/ k = m ) ) as F'. lia.
  rewrite F'. intros [A | B]. apply Hm; trivial. intuition. }
  apply F. split; trivial. apply SI. exact Hm.
Qed.

Goal strongInduction.
Proof.
  intros p SI n.
  pose (Q n := forall k, k < n -> p k).
  assert (Q (S n) -> p n). intro H. apply H. lia.
  apply H. induction (S n). unfold Q. intro k; lia.
  assert (Q n0 /\ p n0 -> Q (S n0)) as F. 
  { intros [Qm Pm]. unfold Q. intros k.
  assert ( (k < S n0) <-> ( k < n0 \/ k = n0 ) ) as F'. lia.
  rewrite F'. intros [A | B]. apply Qm; trivial. intuition. }
  apply F. split.
  apply IHn0. intro Qn0. apply H, F. split. trivial.
  apply SI; unfold Q in Qn0; trivial.
  assert (Q n0). apply IHn0. intro Qn0. apply H, F. split. trivial.
  apply SI; unfold Q in Qn0; trivial.
  apply SI; unfold Q in H0; trivial.
Qed.



Lemma normalizeTerminates : 
  forall T k, k > elements T -> norm' T k = norm' T (elements T).
Proof.
  intros T. induction T.
  - destruct k; cbn; trivial.
  - destruct k; cbn; trivial.
  - destruct k; cbn; trivial.
  - intros k H. assert (k > 0). induction T1; cbn in H; lia. 
    destruct T1. 


Definition normalize (T : gexp) : gexp :=
  match gexpList T with
  | nil => E
  | x :: t => fold_right (fun a b => mult a b) x t
  end.

Compute norm' ( mult (mult ( mult (var 1) (var 2) ) (var 1) ) E ) 4.


Lemma mult_normalize : forall (G: Group)(rho : nat -> G) (t1 t2 : gexp), 
  eval rho (mult (normalize t1) (normalize t2)) = eval rho (normalize (mult t1 t2)).
Proof.
  intros G rho t1. induction t1; intro t2.
  - cbn. rewrite left_neutral. admit.
  - cbn. admit.
  - 
Admitted.

(* Main Theorem *)
Lemma general_asso : forall (G: Group) (t : gexp) (rho : nat -> G), 
  eval rho t = eval rho (normalize t).
Proof.
  intros G t rho. induction t; cbn; try trivial. 
  rewrite IHt2. rewrite IHt1. rewrite <- mult_normalize. cbn. trivial.
Qed.

(* Write procedures that turn some concrete group products into expressions 
with a fitting rho, so that the theorem can be applied to them *)




