Require Import Lia.
Definition dec P := {P} + {~P}.
Definition EQ X := forall x y : X, {x = y} + {x <> y}.

Fixpoint fin n : Type :=
  match n with 
    0 => False 
  | S n' => option (fin n') 
  end.

Fact EQ_option X :
  EQ X -> EQ (option X).
Proof. intros H [x|][y|]; decide equality. Qed.

Fact EQ_fin n : EQ (fin n).
Proof. induction n. {intros []. } now apply EQ_option. Qed.

Fact dec_exists {n} (p: fin n -> Prop) :
  (forall x, dec (p x)) -> (exists x, p x) + (forall x, ~p x).
Proof.
  intros Hdec. induction n as [|n IH].
  {right; intros []. }
  specialize (IH (fun a => p (Some a))) as [IH|IH].
  { intros ?; apply Hdec. }
  - left. destruct IH as [a H].
    exists (Some a). apply H.
  - destruct (Hdec None) as [H|H].
    * left. exists None. apply H.
    * right. intros [a|]. exact (IH a). exact H.
Qed.

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
  x <> x' -> r x = r x' -> f(Some x) = f(Some x').
Proof.
  unfold r; intros ne e.
  generalize (r_spec f H x), (r_spec f H x').
  rewrite <-e.
  generalize (projT1 (R f H x)) as z; fold fin.
  intros ?. clear e; cbn in *. pattern (f None).
  unfold Spec; destruct (f None) as [y0|].
  2: congruence.
  destruct  (f (Some x)) as [y|],
            (f (Some x')) as [y'|].
  * intros [][]; subst; congruence.
  * intros [] ?; subst; congruence.
  * intros ? []; subst; congruence.
  * reflexivity.
Qed.

Lemma Pigeonhole M N (f : fin M -> fin N) :
  M > N -> exists a b, a <> b /\ f a = f b.
Proof.
  revert M f. induction N.
  {intros [] f; [lia | destruct (f None)]. }
  intros [|M] f H_NM; try lia.
  destruct (dec_exists (fun x => f (Some x) = f None)) as [H|H].
  { intros ?; apply EQ_fin. }
  - destruct H as [x ]. exists (Some x), None.
    split; congruence.
  - destruct (IHN _ (r f H) ltac:(lia)) as (x & x'&[]).
    exists (Some x), (Some x').
    split; try congruence.
    eapply r_agree; eauto.
Qed.

Definition injective {X Y} (f : X -> Y) := (forall a b, f a = f b -> a = b).
Lemma inj_leq M N (f : fin M -> fin N) :
  injective f -> M <= N.
Proof.
  revert M f. induction N.
  {intros [] f; [lia | destruct (f None)]. }
  intros [|M] f Inj; try lia.
  destruct (dec_exists (fun x => f (Some x) = f None)) as [H|H].
  { intros ?; apply EQ_fin. }
  - destruct H as [x [=]%Inj].
  - enough (M <= N) by lia.
    apply (IHN _ (r f H)).
    intros x x' E. destruct (EQ_fin _ x x').
    * congruence.
    * enough (Some x = Some x') by congruence.
      eapply Inj, r_agree; eauto.
Qed.