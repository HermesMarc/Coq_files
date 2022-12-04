Require Import Lia.
Load Preamble.


Definition Spec {X Y} (f : option X -> option Y) x r_x :=
  match f None, f(Some x) with
  | None    , _       => f(Some x) = Some r_x
  | Some y0 , None    => r_x = y0
  | Some y0 , Some y  => r_x <> y0 /\ r_x = y
  end.

Definition R {X Y} (f : option X -> option Y) :
  (forall x, f(Some x) <> f None) -> forall x, { r_x & Spec f x r_x}.
Proof.
  unfold Spec; intros H x.
  destruct  (f None) as [y0|] eqn:?,
            (f (Some x)) as [y|] eqn:?.
  - exists y. split; congruence.
  - exists y0. reflexivity.
  - exists y. reflexivity.
  - exfalso. now apply (H x).
Defined.

Definition r {X Y} (f : option X -> option Y) H x := projT1 (R f H x).
Definition r_spec {X Y} (f : option X -> option Y) H x := projT2 (R f H x).

Lemma r_agree {X Y} (f : option X -> option Y) H x x' :
let r := r f H in
  r x = r x' -> f(Some x) = f(Some x').
Proof.
  unfold r; intros e.
  generalize (r_spec f H x), (r_spec f H x').
  rewrite <-e.
  generalize (projT1 (R f H x)) as z.
  intros ?. clear e; unfold Spec.
  destruct (f None) as [y0|]. 2: congruence.
  destruct  (f (Some x)) as [y|],
            (f (Some x')) as [y'|].
  * intros [][]; subst; congruence.
  * intros [] ?; subst; congruence.
  * intros ? []; subst; congruence.
  * intros [][]; reflexivity.
Qed.


Lemma pred_LEM_ {X} (p : X -> Prop) :
  ~~((forall x : X, ~~p x) \/ (exists x, ~p x)).
Proof.
  DN.lem_ (exists x, ~p x). apply DN.ret.
  intros [| H]; auto.
  left. intros x.
  DN.lem_ (p x). apply DN.ret.
  intros []; auto.
  exfalso. apply H.
  now exists x.
Qed.


Lemma Pigeonhole X Y (f : option X -> option Y) :
  (forall g : option Y -> option X, exists x, forall y, g y <> x) -> 
  ~~ exists a b, a <> b /\ f a = f b.
Proof.
  intros nonSurj.
  destruct (nonSurj (fun _ => None)).
  specialize (H None).
  destruct (dec_exists (fun x => f(Some x) = f None)) as [H|H].
  { intros ?; apply EQ_fin. }
  - destruct H as [x ]. exists (Some x), None.
    split; congruence.
  - destruct (IHN _ (r f H) ltac:(lia)) as (x & x' &[]).
    exists (Some x), (Some x').
    split; try congruence.
    eapply r_agree; eauto.
Qed.