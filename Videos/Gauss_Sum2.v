

Inductive Likes : Type := O | L : Likes -> Likes.


Fixpoint add x y := 
  match x with
  | O => y
  | L n => L (add n y)
  end.

Fixpoint mult x y := 
  match x with 
  | O => O
  | L n => add y (mult n y)
  end.

Notation "x ⊕ y" := (add x y) (at level 50).
Notation "x ⊗ y" := (mult x y) (at level 40).

Fixpoint Σ N := 
  match N with
  | O => O
  | L n => N ⊕ (Σ n)
  end.



Lemma add_O_r x: x ⊕ O = x.
Proof.
  induction x.
  - reflexivity.
  - cbn. rewrite IHx. reflexivity.
Qed.

Lemma add_L_r x y : x ⊕ L y = (L x) ⊕ y.
Proof.
  induction x.
  - cbn. reflexivity.
  - cbn. rewrite IHx. reflexivity.
Qed.


Lemma add_comm x y : x ⊕ y = y ⊕ x.
Proof.
  induction x.
  - cbn. rewrite add_O_r. reflexivity.
  - cbn. rewrite IHx. rewrite add_L_r. reflexivity.
Qed.


Lemma add_asso x y z : (x ⊕ y) ⊕ z = x ⊕ (y ⊕ z).
Proof.
  induction x.
  - cbn. reflexivity.
  - cbn. rewrite IHx. reflexivity.
Qed.


Lemma mult_distr_l x y z : x ⊗ (y ⊕ z) = x ⊗ y ⊕ x ⊗ z.
Proof.
  induction x; cbn.
  - reflexivity.
  - rewrite IHx.
    rewrite <-add_asso, (add_asso y).
    rewrite (add_comm z).
    rewrite !add_asso.
    reflexivity.
Qed.


Lemma mult_O_r x : x ⊗ O = O.
Proof.
  induction x; cbn.
  - reflexivity.
  - apply IHx.
Qed.

Lemma mult_L_r x y : x ⊗ (L y) = x ⊕ x ⊗ y.
Proof.
  induction x; cbn.
  - reflexivity.
  - rewrite IHx. 
    rewrite <- add_asso.
    rewrite (add_comm y x).
    rewrite add_asso.
    reflexivity.
Qed.

Lemma mult_comm x y : x ⊗ y = y ⊗ x.
Proof.
  induction x; cbn.
  - rewrite mult_O_r. reflexivity.
  - rewrite mult_L_r. rewrite IHx. reflexivity.
Qed.


Theorem Gauss_Sum N : (L (L O)) ⊗ Σ N = N ⊗ L N.
Proof.
  induction N.
  - cbn. reflexivity.
  - cbn [Σ]. 
    rewrite mult_distr_l.
    rewrite IHN.
    rewrite !(mult_comm _ (L N)).
    rewrite <- mult_distr_l.
    cbn [add].
    reflexivity.
Qed.