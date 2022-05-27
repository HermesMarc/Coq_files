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
Proof. induction n. {intros []. }  now apply EQ_option. Qed.

Fact fin_dec {n} (p: fin n -> Prop) :
  (forall x, dec (p x)) -> (forall x, ~p x) + (exists x, p x).
Proof.
  intros Hdec. induction n as [|n IH].
  {left; intros []. }
  specialize (IH (fun a => p (Some a))) as [IH|IH].
  { intros ?; apply Hdec. }
  - destruct (Hdec None) as [H|H].
    * right. exists None. apply H.
    * left. intros [a|]. exact (IH a). exact H.
  - right. destruct IH as [a H].
    exists (Some a). apply H.
Qed.

(*  Proof of the Pigeonhole principle
*)
Definition R {X Y} (f : option X -> option Y) :
  (forall x, f(Some x) <> f None) ->
  forall x, { r_x &
    match f None, f(Some x) with
    | None    , _       => f(Some x) = Some r_x
    | Some y0 , None    => r_x = y0
    | Some y0 , Some y  => r_x <> y0 /\ r_x = y
    end}.
Proof.
  intros H x.
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
  x <> x' -> r f H x = r f H x' -> f(Some x) = f(Some x').
Proof.
  intros ne e.
  generalize (r_spec f H x), (r_spec f H x').
  unfold r in e. rewrite <-e.
  generalize (projT1 (R f H x)) as z; fold fin.
  intros ?. clear e; cbn in *. pattern (f None).
  destruct (f None) as [y0|] eqn:f0.
  2: congruence.
  destruct  (f (Some x)) as [y|], (f (Some x')) as [y'|].
  * now intros [? <-][? <-].
  * intros [? <-] ->. exfalso. congruence.
  * intros -> [? <-]. exfalso. congruence.
  * congruence.
Qed.

Lemma Pigeonhole M N (f : fin M -> fin N) :
  M > N -> exists a b, a <> b /\ f a = f b.
Proof.
  revert M f. induction N.
  {intros [] f; [lia | destruct (f None)]. }
  intros [|M] f H_NM; try lia.
  destruct (fin_dec (fun x => f (Some x) = f None)) as [h|h].
  { intros ?; apply EQ_fin. }
  - destruct (IHN _ (r f h) ltac:(lia)) as (x & x' & ne & e).
    exists (Some x), (Some x'). 
    split; try congruence.
    eapply r_agree; eauto.
  - destruct h as [x Hx]. exists (Some x), None.
    split; congruence.
Qed.