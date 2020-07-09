(* Minimal Logic *)

Section Minimal.

  (* We try to work in a logic without False and use this varible in place of False *)
  Variable C : Prop.
  
  Definition LEM : Prop := forall X : Prop , or (X -> C) X.
  Definition DN : Prop := forall X : Prop, ((X -> C) -> C) -> X.
  Definition CP : Prop := forall X Y : Prop, ((Y -> C) -> (X -> C)) -> X -> Y.

  Definition Peirce : Prop := forall X Y : Prop, ((X -> Y) -> X) -> X.

  Lemma TN : forall X, (((X -> C) -> C) -> C) <-> (X -> C).
  Proof.
    split.
    - intros nnnX x. apply nnnX. intros nX. apply nX. exact x.
    - intros nX nnX. apply nnX. exact nX.
  Qed.

  Lemma DN_LEM : DN -> LEM.
  Proof.
    - intros dn X. apply dn. intro H. apply H. left. intro x. 
      apply H. right; trivial.
  Qed.

  Lemma DN_CP : DN <-> CP.
  Proof.
    split.
    - intros dn X Y cp x. apply dn. intro nY. apply cp. exact nY. exact x.
    - intros cp X. apply cp. intros nX nnX. apply nnX. exact nX. 
  Qed.

  Lemma CP_Peirce : CP -> Peirce.
  Proof.
    intros cp X Y. apply cp. intros notX H. apply notX, H. apply cp.
    intro. exact notX.
  Qed.


  Lemma Peirce_LEM : Peirce -> LEM.
  Proof.
    intros peirce X. apply (peirce _ C). intro H. left. intro x. 
    apply H. right. exact x.
  Qed.


  Lemma DN_Peirce : DN -> Peirce.
  Proof.
    intros dn X Y. intros G. apply dn. intros nX. apply nX, G. intros x.
    apply dn. intros nY. apply nX. exact x.
  Qed.


  Lemma CP_LEM : CP -> LEM.
  Proof.
    intros cp X. apply (cp True _ ). intros H.
    assert (C -> (True -> C) ) as HC.
    {intros c I. exact c. }
    apply HC. apply H. left. intro x. apply H; tauto. exact I.
  Qed.

End Minimal.


(* The above statements are equivalent in intuitionistic logic, 
when we take C = False. We only show the missing implications. *)


Definition LEM' : Prop := LEM False.

Definition DN' : Prop := DN False.

Definition CP' : Prop := CP False.


Lemma TN' : forall X:Prop, ~ ~ ~X <-> ~X.
Proof.
  split.
  - intros nnnX x. apply nnnX. intros nX. apply nX. exact x.
  - intros nX nnX. apply nnX. exact nX.
Qed.


Goal LEM' -> DN'.
Proof.
  intros lem X nnX. destruct (lem X) as [nX | x].
  contradiction (nnX nX). exact x.
Qed.


Goal Peirce <-> CP'.
Proof.
  split.
  - intros peirce X Y H x. apply (peirce _ False). intro nY. exfalso. 
    apply H; trivial.
  - apply CP_Peirce.
Qed.


Goal LEM' <-> Peirce.
Proof.
  split.
  - intros lem X Y H. destruct (lem X) as [nX | x].
    apply H. intro x. exfalso. apply nX. all : trivial.
  - apply Peirce_LEM.
Qed.


Goal Peirce <-> DN'.
Proof.
  split.
  - intros peirce X nnX. apply (peirce _ False). intro nX. contradiction.
  - apply DN_Peirce.
Qed.


Goal LEM' <-> CP'.
Proof.
  split.
  - intros lem X Y H x. destruct (lem Y) as [nY | y].
    exfalso. apply H; tauto. tauto.
  - apply CP_LEM.
Qed.
