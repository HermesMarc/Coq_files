Require Import Arith Lia Lists.List.
Import ListNotations.


Section Hom.

  Variable M : Type.
  Variable e : M.
  Variable o : M -> M -> M.
  Infix "⊙" := o (at level 50).

  Hypothesis neutral_r : forall m, m ⊙ e = m. 
  Hypothesis neutral_l : forall m, e ⊙ m = m.
  Hypothesis asso : forall x y z, (x ⊙ y) ⊙ z = x ⊙ (y ⊙ z).

  Implicit Type f : list nat -> M.
  Implicit Type g : nat -> M.

  Definition list_hom f := f nil = e /\ forall A B, f(A ++ B) = f(A) ⊙ f(B).
  

  Lemma e_unique x : (forall m, m ⊙ x = m \/ x ⊙ m = m) -> x = e.
  Proof.
    intros H. specialize (H e) as [<-|<-].
    all: symmetry. apply neutral_l. apply neutral_r.
  Qed.


  Fixpoint foldr (g : nat -> M -> M) m A := 
    match A with 
    | nil => m
    | x :: L => g x (foldr g m L)
    end.

  Fixpoint foldl (g : M -> nat -> M) m A := 
  match A with 
  | nil => m
  | x :: L => g (foldl g m L) x
  end.




End Hom.