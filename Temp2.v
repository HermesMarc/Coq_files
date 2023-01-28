Load Preamble.


Definition FE := forall X Y (g f : X -> Y), (forall x, f x = g x) -> f = g.

Lemma Stab_func_eq X B : 
  FE -> (forall a b : B, stable (a = b)) -> forall f g : X -> B, stable (f = g).
Proof.
  intros fe H f g nnH.
  apply fe. intros x.
  apply H. apply (DN.remove nnH).
  now intros ->.
Qed.



Section type.
  Variable F : Type.
  Definition LEM_T := forall (A : Type), sum A (A -> F).
  Definition PL_T := forall (A B : Type), ((A -> B) -> A) -> A.

  Goal PL_T -> LEM_T.
  Proof.
    intros H A.
    refine (H _ F _). intros h.
    right. intros a. apply h. now left.
  Qed.
End type.


Definition PL := forall B A, ((A -> B) -> A) -> A.
Definition sDN := forall B A, ((A -> B) -> B) -> A.


Lemma much_PL :
  forall A B C D E F, (E -> B) -> (E -> F) -> (A -> D) -> (C -> D) -> 
  ((((A -> B) -> C) -> D) -> E) -> F.
Proof.
  intros A B C D E F H0 H1 H2 H3 H4. apply H1, H4. 
  intros H5. apply H3, H5.
  intros a. apply H0, H4.
  intros _. apply H2, a.
Qed.


Goal sDN -> PL.
Proof.
  intros dn F A. apply (dn F). tauto.
Qed.

Goal forall F, (forall A, ((A -> F) -> F) -> A) -> PL.
Proof.
  intros F H A B. apply H.
  refine (fun f => f (fun g => g (fun a => _))).
  apply H; tauto.
Qed.


Lemma PL_equiv : 
 PL <=> (forall A B C D, (A -> D) -> (C -> D) -> ((A -> B) -> C) -> D).
Proof.
  split; intros pl.
  - intros A B C D ???.
    apply (pl B). tauto.
  - intros B A. now apply pl.
Qed.


Goal PL <=> (forall F A, (F -> A) -> ((A -> F) -> F) -> A).
Proof.
  split; intros pl.
  - intros F A. now apply PL_equiv.
  - intros F A. apply (pl F); tauto.
Qed.


Goal PL <=> (forall A, (False -> A) -> ((A -> False) -> False) -> A).
Proof.
  split; intros pl.
  - intros A. now apply PL_equiv.
  - intros B A. apply pl; tauto.
Qed.


Section FixF.

  Variable F : Type.

  (* If the F-negation of A implies A, then we have A *)
  Definition wPL := forall A, ((A -> F) -> A) -> A.
  Definition Expl := forall A, F -> A.
  Definition DN := forall A, ((A -> F) -> F) -> A.

  Goal DN -> Expl * PL.
  Proof.
    intros dn; split.
    - intros ??. apply dn. tauto.
    - intros A B. apply dn.
      refine (fun f => f (fun g => g (fun a => _))).
      apply dn; tauto.
  Qed.

  Goal  Expl * PL -> DN.
  Proof.
    intros [expl pl].
    intros A ?.
    apply (pl F). intros ?.
    apply (pl A), expl. tauto.
  Qed.

  Goal DN -> Expl * wPL.
  Proof.
    intros dn. split.
    - intros A ?. apply (dn A). tauto.
    - intros A. apply dn. tauto.
  Qed.

  Goal Expl * wPL -> DN.
  Proof.
    intros [expl pl] A ?.
    apply (pl A). intros ?.
    apply expl. tauto.
  Qed.

End FixF.


Section FixF.

  Variable F : Type.
  Notation "¬ A" := (A -> F) (at level 10).

  Definition Expl' := forall A, ¬ ¬ (F -> A).
  Definition DN' := forall A, ¬ ¬ (((A -> F) -> F) -> A).

  Goal DN' -> Expl'.
  Proof.
    intros dn.
    intros A ?. apply (dn A). tauto.
  Qed.

  Goal Expl' -> DN'.
  Proof.
    intros expl A H.
    enough (pl : forall A, ¬ ¬ (((A -> F) -> A) -> A )).
    - eapply pl. intros pl'.
      eapply expl. intros expl'.
      apply H. intros ?.
      apply (pl'). intros ?.
      apply expl'. tauto.
    - intros. tauto.
  Qed.


  Inductive Three := one | two | three.
  Definition P A := (A -> F) -> A.
  Definition E A := (F -> A) -> F.
  Definition Id (A : Type) := A.

  Definition Tr n := 
    match n with
    | one => P
    | two => E
    | three => Id
    end.

  (* The below shows that having E everywhere is the only candidate that make Peirce work *)
  Goal forall A B a b, (((Tr a A) -> (Tr b B)) -> (Tr b A)) -> Tr b A.
  Proof.
    intros A B [][]; unfold Tr.  
    5: unfold E; tauto.
    all: unfold P, E, Id. 
    all: try tauto.
  Admitted.

  Goal forall A B, (((E A) -> (E B)) -> (E A)) -> E A.
  Proof.
    intros A B; unfold Tr, P, E, Id. try tauto.
  Qed.

  Goal forall A B, E (A -> B) -> (E A) -> (E B).
  Proof.
    intros A B. unfold E; try tauto.
  Qed.

  Goal forall A B, E (A + B) -> ((E A) + (E B)).
  Proof.
    intros A B. unfold E; try tauto.
  Qed.

  Goal forall A B, (E A) * (E B) -> E (A * B).
  Proof.
    intros A B. unfold E; try tauto.
  Qed.

  Goal forall A, E (E A) -> E A.
  Proof.
    intros A. unfold E; try tauto.
  Qed.

  Goal forall X (p : X -> Type) (a : X),
    (forall x, E (p x)) -> E (forall x, p x).
  Proof.
    intros X p a H exp. firstorder.
  Qed.

  Goal forall X (p : X -> Type) (a : X),
    E (Sigma x, p x) -> (Sigma x, E (p x)).
  Proof.
    unfold E. intros X p a H. exists a. intros h.
    apply H. intros f%h. now exists a.
  Qed.

  Goal forall A, ((E A -> F) -> F) -> E A.
  Proof.
    intros A; unfold E; try tauto.
  Qed.



End FixF.