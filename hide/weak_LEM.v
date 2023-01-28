
Definition wLEM := forall X, ~~X \/ ~X.
Definition wLIN := forall A B C : Prop, ~~(A -> B) \/ (B -> A).
(* is itself again equivalent to forall A B C : Prop, ~~(A -> B) \/ ~~(B -> A) *)
Definition wSLIN := forall A B C : Prop, ~~(A -> B) \/ (B -> C).

Goal wLEM <-> wLIN.
Proof.
  split.
  - intros H A B C. 
    destruct (H B); tauto.
  - intros H X. destruct (H X (~X)); tauto.
Qed.

Goal wLEM <-> wSLIN.
Proof.
  split.
  - intros wlem A B C.
    destruct (wlem B) as [H|H]; tauto.
  - intros sl X.
    specialize (sl True X False).
    tauto.
Qed.

Goal wLEM <-> forall A B, ~~(A \/ B) -> ~~A \/ ~~B.
Proof.
  split.
  - intros wlem A B H. destruct (wlem A); tauto.
  - intros H P. specialize (H P (~P)); tauto.
Qed.

Goal wLEM <-> forall A B : Prop, ~~(A -> B) -> ~~B \/ ~A.
Proof.
  split.
  - intros wlem A B H. destruct (wlem A); tauto.
  - intros H P. specialize (H P P); tauto.
Qed.

Goal forall A B : Prop,  ~~B \/ ~A -> ~~(A -> B).
Proof.
  intros. tauto.
Qed.

Definition Distr :=
  forall A B C : Prop, ((A /\ B) -> C) -> (A -> C) \/ (B -> C).

Goal Distr -> wLEM.
Proof.
  intros distr ?. now apply distr.
Qed.



Lemma pred_wLEM :
  wLEM <-> forall X p, (forall x : X, ~~p x) \/ ~~(exists x, ~p x).
Proof.
  split.
  - intros wlem X p.
    destruct (wlem (exists x, ~p x)) as [| H]; auto.
    left. intros x.
    destruct (wlem (p x)); auto.
    exfalso. apply H.
    now exists x.
  - intros H X.
    specialize (H Prop (fun _ => ~X)) as [].
    + right. tauto.
    + left. intros nH. apply H.
      intros []; tauto.
Qed.

Lemma pred_wLEM_ {X} p :
  wLEM -> (forall x : X, ~~p x) \/ ~~(exists x, ~p x).
Proof.
  intros wlem.
    destruct (wlem (exists x, ~p x)) as [| H]; auto.
    left. intros x.
    destruct (wlem (p x)); auto.
    exfalso. apply H.
    now exists x.
Qed.


Goal forall X (p : X -> Prop), 
X -> ~~ exists x : X, (p x -> forall y, ~~p y).
Proof.
  intros X p x.
  intros nH. apply nH.
  exists x. intros _ y py. 
  apply nH. exists y. tauto.
Qed.

Goal wLEM -> forall X (p : X -> Prop), 
X -> exists x : X, ~~p x -> forall y, ~~p y.
Proof.
  intros wlem X p x.
  destruct (pred_wLEM_ p wlem) as [|H].
  firstorder. exact True.
  exists x. intros px y py. apply H.
  intros [].
Admitted.


Goal (forall X (p : X -> Prop), X -> exists x : X, (p x -> forall y, ~~p y)) -> wLEM.
Proof.
  intros H X.
  specialize (H bool (fun x => if x then X else ~X) true) as [[] H].
  - right. intros ?.
    refine (H _ false _). all: tauto.
  - left. intros ?.
    refine (H _ true _). all: tauto.
Qed.


Goal ~~(forall P, ~~P -> P) -> (forall X (p : X -> Prop) (a : X),  ~~ exists x : X, ~~ p x -> forall y, p y).
Proof.
  intros ndne X p a H.
  apply ndne. intros dne.
  apply H. exists a.
  intros _ y. apply dne. intros npy.
  apply H. exists y. intros py.
  tauto.
Qed.


Goal (forall X (p : X -> Prop) (a : X),  ~~ exists x : X, ~~ p x -> forall y, p y) -> ~~(forall P, ~~P -> P).
Proof.
  intros nnH.
  specialize (nnH _ (fun X => ~~X -> X) True).
  intros ndne.
  apply nnH. intros [P H]. apply ndne.
  apply H; tauto.
Qed.


Definition all {X} (p : X -> Prop) := forall x : X, p x.
Definition PL := forall A B : Prop, ((A -> B) -> A) -> A.

(* This proof only uses PL. No explosion required. *)
Goal PL -> forall X (p : X -> Prop),
  (forall x, (p x -> all p) -> p x) -> all p.
Proof.
  intros PL X p H y.
  eapply (PL _ (all p)), H.
Qed.


(* Here is a small generalization which is equivalent to PL even in minimal logic. *)
Goal PL <-> forall X (p q : X -> Prop),
  (forall x, (p x -> all q) -> p x) -> all p.
Proof.
  split.
  - intros PL X p q H y.
    apply (PL _ (all q)). apply H.
  - intros drinker A B H.
    specialize (drinker Prop (fun _ => A) (fun _ => B)). 
    unfold all in *; tauto.
Qed.


Goal PL <-> forall X (p q : X -> Prop), 
  (forall x, (exists y, p x -> q y) -> p x) -> all p.
Proof.
  split.
  - intros PL X p q H y.
    apply (PL _ (q y)). intros h.
    apply H. exists y. apply h.
  - intros drinker A B H.
    specialize (drinker Prop (fun _ => A) (fun _ => B)). 
    unfold all in *. apply drinker.
    intros _ [_ ]. all: tauto. 
Qed.


Goal PL <-> forall X (p : X -> Prop) (B : Prop), 
  (forall x, (p x -> B) -> p x) -> all p.
Proof.
  split.
  - intros PL X p B H y.
    apply (PL _ B). intros h.
    apply H, h.
  - intros drinker A B H.
    specialize (drinker Prop (fun _ => A) B). 
    unfold all in *. apply drinker.
    intros _. all: tauto. 
Qed.


Goal PL <-> forall X (p : X -> Prop) (A : Prop) (a : X), 
  ((exists x, A -> p x) -> A) -> A.
Proof.
  split.
  - intros PL X p A a H.
    apply (PL _ (p a)). intros h.
    apply H. now exists a.
  - intros drinker A B H.
    specialize (drinker Prop (fun _ => B) A True). 
    unfold all in *. apply drinker.
    intros []. tauto.
Qed.


Goal (forall X (p : X -> Prop),
  forall y, exists x, ~~ p y \/ ~ p x) <-> wLEM.
Proof.
  split.
  - intros H A.
    specialize (H Prop (fun _ => A)) as [_ H]; tauto.
  - intros wlem X p a.
    exists a. apply wlem.
Qed.



Goal (forall X (p : X -> Prop) (a : X),
  exists x, ~~ forall y, ~~ p y \/ ~ p x) <-> wLEM.
Proof.
  split.
  - intros H A.
    specialize (H Prop (fun _ => A) True).
    admit.
  - intros wlem X p a.
    exists a. intros nH. apply nH.
    destruct (wlem (p a)); auto.
    intros y. left. intros npy.
Admitted. 


Goal (forall X (p : X -> Prop) (a : X),
  ~~ exists x, forall y, ~~ (p x -> p y)) <-> wLEM.
Proof.
  split.
  - intros H A.
    specialize (H Prop (fun x => x) True).
    admit.
  - intros wlem X p a.
    destruct (pred_wLEM_ p wlem).
    + intros nG. apply nG. exists a.
      intros. firstorder.
    + intros nG. apply nG. exists a. intros y nH.
      apply H. intros [x npx].
      apply nG. exists x. tauto.
Qed.