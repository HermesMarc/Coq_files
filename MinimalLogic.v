(* Minimal Logic *)

Definition iffT (X Y : Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).


Section Minimal.

  (* We try to work in a logic without False and use the variable F in its place *)
  Variable F : Type.

  Definition Contradiction := forall A B, (A -> F) -> A -> B.
  Definition Explosion := forall A, F -> A. 
  Definition LEM := forall A, A + (A -> F).
  Definition DN := forall A, ((A -> F) -> F) -> A.
  Definition CP := forall A B, ((B -> F) -> (A -> F)) -> A -> B.

  Definition Peirce := forall A B, ((A -> B) -> A) -> A.


  Goal Contradiction <=> Explosion.
  Proof.
    split.
    - intros con A. apply con. auto.
    - intros expl. intros A B H a. apply expl. auto.
  Qed.
  

  Goal DN -> Explosion.
  Proof.
    intros dn A f. apply dn. intros H. exact f.
  Qed.


  Goal LEM * Explosion -> DN.
  Proof.
    intros [lem exp] X nnX. destruct (lem X) as [x | H]. exact x.
    apply exp. apply nnX. exact H.
  Qed.

  
  Lemma DN_CP : DN <=> CP.
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
    intros peirce X. apply (peirce _ F). intro H. right. intros x. apply H.
    left. exact x. 
  Qed.


End Minimal.


(* The above statements are equivalent in intuitionistic logic, 
when we take F = False. We now show the missing equivalences. *)


Definition LEM' := LEM False.
Definition DN' := DN False.
Definition CP' := CP False.


Goal Peirce <=> CP'.
Proof.
  split.
  - intros peirce X Y H x. apply (peirce _ False). intro nY. exfalso. 
    apply H; trivial.
  - apply CP_Peirce.
Qed.


Goal LEM' <=> Peirce.
Proof.
  split.
  - intros lem X Y H. destruct (lem X) as [x | nX].
    exact x. apply H. intro x. exfalso. apply nX. exact x.
  - apply Peirce_LEM.
Qed.
