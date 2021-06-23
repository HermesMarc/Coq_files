(* 

This documents presents 3 different proofs (in the order they were conceived) of the fact that if option X and option Y are in bijection, then so are X and Y.  

*)

Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.
Notation p1 := projT1.

Definition inv {X Y} g (f: X -> Y) := forall x, g (f x) = x.

Inductive Bij (X Y : Type) : Type :=
| Bijection: forall (f: X -> Y) (g: Y -> X), inv f g -> inv g f -> Bij X Y.

Arguments Bijection {X Y}.


(* Proof by Marc Hermes using a rewiring function and informative sigma types to get the desired extractions *)

Definition rewire {X Y} (f : option X -> option Y) :=
  fun ox =>
  match ox with
  | None => None
  | Some x => match f (Some x) with
              | None => f None
              | Some y => Some y
  end end.

Section Lemmas.
  Variables X Y : Type.
  Variable f : option X -> option Y.
  Variable g : option Y -> option X.

Lemma inv_rewire :
  inv g f -> inv (rewire g) (rewire f).
Proof.
  intros gf. unfold rewire.
  intros [x|]; auto.
  destruct (f (Some x)) as [y|] eqn:f_some; cbn.
  - now rewrite <-f_some, gf.
  - destruct (f None) as [y|] eqn:f_none.
    + rewrite <-f_none, gf. congruence.
    + congruence.
Qed.

Definition extract {A B} h := forall x : A, Sigma y : B, h (Some x) = Some y.

Lemma inv_extract (F : extract f) (G : extract g) : 
  inv g f -> inv (fun y => projT1 (G y)) (fun x => projT1 (F x)).
Proof.
  intros gf x.
  destruct (F x) as [y ]; cbn.
  destruct (G y) as [x' ]; cbn.
  congruence.
Qed.

Lemma extraction (F : option X -> option Y) :
  (forall ox, F ox = None -> ox = None) -> extract F.
Proof.
  intros H x.
  destruct (F (Some x)) as [y|] eqn:H_some.
  - exists y. reflexivity.
  - apply H in H_some. discriminate.
Qed.

Lemma extract_rewire :
  inv g f -> extract (rewire f).
Proof.
  intros gf. apply extraction.
  intros [x|]; [|reflexivity].
  unfold rewire.
  destruct (f (Some x)) eqn:?; congruence.
Qed.
End Lemmas.

Arguments extract_rewire {X Y f g}.

Lemma bij_option X Y :
  Bij (option X) (option Y) -> Bij X Y.
Proof.
  intros [F G FG GF].
  specialize (extract_rewire GF) as f.
  specialize (extract_rewire FG) as g.
  exists (fun x => projT1 (f x)) (fun y => projT1 (g y)).
  - apply inv_extract, inv_rewire, FG.
  - apply inv_extract, inv_rewire, GF.
Qed.



(* Proof due to Yannick Forster and Andrej Dudenhefner; making use of and illustrating how to handle dependant typing *)

Lemma no_confusion {X} {Y} {f : option X -> option Y} {g} :
  inv g f -> forall x, f (Some x) <> f None.
Proof. congruence. Qed.

Definition R {X} {Y} (f : option X -> option Y) g :
  inv g f -> X -> Y :=
    fun (H : inv g f) (x : X) =>
  match (f (Some x)) as oy return (oy <> f None -> Y) with
  | Some y => fun _ => y
  | None => fun Hf =>
    match (f None) as oy' return (None <> oy' -> Y) with
    | Some y' => fun _ => y'
    | None => fun H' => match H' eq_refl return Y with end
    end Hf
  end (no_confusion H x).

Lemma elim_R {X Y : Type} (f : option X -> option Y) g H x {p : Y -> Prop} : 
  (forall y, f (Some x) = Some y -> p y) ->
  (forall y', f (Some x) = None -> f None = Some y' -> p y') -> p (R f g H x).
Proof.
  intros H1 H2. unfold R. generalize (no_confusion H x).
  intros Hf.
  destruct (f (Some x)).
  - now apply H1.
  - destruct (f None).
    + now apply H2.
    + easy.
Qed.

Lemma spec {X} {Y} (f : option X -> option Y) g :
  forall (H1 : inv g f) (H2 : inv f g),
  inv (R f g H1) (R g f H2).
Proof.
  intros H1 H2 y.
  pattern (R g f H2 y). apply elim_R.
  - intros x Hx.
    pattern (R f g H1 x). apply elim_R.
    + intros y' Hy'. congruence.
    + intros y' Hy'. congruence.
  - intros x Hx.
    pattern (R f g H1 x). apply elim_R.
    + intros y' Hy'. congruence.
    + intros y' Hy'. congruence.
Qed.



(* This final and most succint proof was later devised by Prof. Gert Smolka *)

Fact Rewire {X Y f g} :
  @inv (option X) (option Y) g f ->
  forall x, Sigma y, match f (Some x) with Some y' => y = y' | None => f None = Some y end.
Proof.
  intros H x.
  destruct (f (Some x)) as [y|] eqn:E1.
  - exists y. reflexivity.
  - destruct (f None) as [y|] eqn:E2.
    + exists y. reflexivity.
    + exfalso. congruence.
Qed.

Fact Rewire_inv {X Y} (f : option X -> option Y) g :
  forall (H1: inv g f) (H2: inv f g),
    inv (fun y => p1 (Rewire H2 y)) (fun x => p1 (Rewire H1 x)).
Proof.
  intros H1 H2 x.
  destruct (Rewire H1 x) as [y H3]; cbn.
  destruct (Rewire H2 y) as [x' H4]; cbn.
  destruct (f (Some x)) as [y1|] eqn:E3;
    destruct (g (Some y)) as [x1|] eqn:E1;
    congruence.
Qed.