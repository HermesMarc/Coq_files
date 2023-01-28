Load Preamble.

Definition LEM := forall X, X \/ ~X.
Definition wLEM := forall X, ~X \/ ~~X.
Definition DNE := forall X, ~~X -> X.


Lemma constr_Eater X (p : X -> Prop) :
  forall a:X, ~~ exists x, p x -> forall y, ~~ p y.
Proof.
  intros a H. apply H.
  exists a. intros _ y npy.
  apply H. exists y. intros py.
  destruct (npy py).
Qed.


Goal
  (forall X p, (forall x:X, ~~p x) -> forall y, p y) -> DNE.
Proof.
  intros H P. pattern P. apply H; tauto.
Qed.

Goal
  DNE -> (forall X p, (forall x:X, ~~p x) -> forall y, p y).
Proof.
  intros dne X p H y. apply dne, H.
Qed.

Goal forall X (p : X -> Prop) (C : Prop) (a:X),
  ((forall x, ~~p x) -> C) -> ~~(exists x, p x -> C).
Proof.
  intros X p C a H nh.
    assert (forall x, ~ (p x -> C)) as h by firstorder.
    apply (h a). intros _.
    apply H. intros x npx.
    apply (h x). tauto.
Qed.

Goal forall X (p : X -> Prop) (C : Prop),
  ~~(exists x, p x -> ~C) <-> (forall x, ~~p x) -> ~C.
Proof.
  firstorder.
Qed.



Goal
  DNE -> (forall X (p : X -> Prop) (C : Prop) (a:X), ((forall x, p x) -> C) -> (exists x, p x -> C)).
Proof.
  intros dne X p C a H.
  apply dne. intros nh.
  assert (forall x, ~ (p x -> C)) as h by firstorder.
  apply (h a). intros _.
  apply H. intros x.
  apply dne. intros npx.
  apply (h x). tauto.
Qed.

Goal
  (forall X p (C : Prop), ((forall x:X, p x) -> C) -> (exists x, p x -> C)) -> wLEM.
Proof.
  intros H P.
  specialize (H bool (fun b => if b then P else ~P) False); cbn in *.
  destruct H as [[] ]; try tauto.
  intros H. apply (H false). apply (H true).
Qed.