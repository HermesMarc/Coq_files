(*  Slightly modified version of the Drinker's Paradox, making it equivalent 
    to DNE, LEM and similar statements in the constructive Logic of Coq. 
*)


Definition Eater := forall X (p : X -> Prop), 
  forall a : X, exists x, (~~p x -> forall y, p y).

Definition classical q : Prop := forall P : Prop, ~~ q P.
Definition constructive (q : Prop -> Prop) := forall P : Prop, q P.

Lemma Eater_cl q : classical q -> Eater -> constructive q.
Proof.
  intros Hq eater X.
  specialize (eater _ q) as [P H]; auto.
Qed.


Section DNE.

  Definition stable X := ~~ X -> X.
  Definition DNE := forall X, stable X.

  Goal DNE -> Eater.
  Proof.
    intros dnE X p x.
    apply dnE.
    intros nH. apply nH.
    exists x.
    intros _ y. apply dnE.
    intros ?. apply nH.
    exists y. tauto.
  Qed.

  Goal Eater -> DNE.
  Proof.
    refine (Eater_cl _ _).
    unfold classical, stable. tauto.
  Qed.

End DNE.


Section LEM.

  Definition definite X := X \/ ~X.
  Definition LEM := forall X, definite X.

  Lemma pred_LEM {X} (p : X -> Prop) :
    LEM -> (forall x, p x) \/ (exists x, ~p x).
  Proof.
    intros lem.
    destruct (lem (exists x, ~p x)) as [| H]; auto.
    left. intros x.
    destruct (lem (p x)); auto.
    exfalso. apply H.
    now exists x.
  Qed.

  Goal LEM -> Eater.
  Proof.
    intros lem X p x.
    destruct (pred_LEM p lem) as [|H].
    - exists x. tauto.
    - destruct H as [d ].
      now exists d.
  Qed.

  Goal Eater -> LEM.
  Proof.
    refine (Eater_cl _ _).
    unfold classical, definite. tauto.
  Qed.

End LEM.