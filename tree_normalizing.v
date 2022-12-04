Require Import Lia.

Inductive tree : Type :=
| o : tree
| T : tree -> tree -> tree.


Fixpoint branches (t : tree) :=
match t with
| o => 0
| T t1 t2 => 1 + (branches t1) + (branches t2)
end.


Fixpoint normal (T : tree) : Prop :=
match T with
| o => True
| T o t => normal t
| _ => False
end.


Inductive Eq : tree -> tree -> Prop :=
| EqRef : forall t, Eq t t
| EqSym : forall s t, Eq s t -> Eq t s
| EqTran : forall x y z, Eq x y -> Eq y z -> Eq x z
| EqAsso : forall t1 t2 t3, Eq ( T (T t1 t2) t3 ) (T t1 (T t2 t3) )
| EqT : forall t1 t2 s1 s2, Eq t1 s1 -> Eq t2 s2 -> Eq (T t1 t2) (T s1 s2).


Require Import Setoid Morphisms.

Instance : Equivalence Eq.
Proof.
  split.
  intros t. exact (EqRef t).
  intros s t H. apply EqSym; auto.
  intros x y z H1 H2. exact (EqTran x y z H1 H2).
Defined.


Instance T_congruent :
  Proper (Eq ==> Eq ==> Eq) T.
Proof.
  intros t s Eq t' s' Eq'. apply EqT; auto.
Qed.


Instance branch_congruent :
  Proper (Eq ==> (@eq nat)) branches.
Proof.
  intros t s H. induction H; cbn; lia.
Qed.
  

Lemma free_leaf t : 
  t <> o -> (exists t', Eq t (T o t') ).
Proof.
  intros noLeaf. induction t. now exists o.
  destruct t1.
  - now exists t2.
  - assert (T t1_1 t1_2 <> o) as H by discriminate.
    destruct (IHt1 H) as [t' H']. exists (T t' t2).
    now rewrite H', EqAsso.
Qed.


Lemma ex_iff {X} (P Q : X -> Prop) :
  (forall x, P x <-> Q x) -> (exists x, P x) <-> (exists x, Q x).
Proof.
  firstorder.
Qed.

Theorem pre_normalization : forall (n: nat)(t : tree), 
  branches t < n -> exists t', normal t'  /\ Eq t t'.
Proof.
  induction n. destruct t; cbn; lia.
  destruct t; intro Bran. exists o; cbn; split. auto. apply EqRef.
  cbn in Bran. destruct t1.
  - assert (branches t2 < n) as H by lia. 
    destruct (IHn _ H) as [s [? E]].
    exists (T o s). split; cbn; try tauto.
    rewrite E; apply EqRef.
  - assert (T t1_1 t1_2 <> o) as  Triv by discriminate.
    destruct ( free_leaf (T t1_1 t1_2) Triv ) as [t1 N1].
    eapply (ex_iff (fun x => normal x /\ Eq (T (T o t1) t2) x)).
    { intros x. now rewrite N1. }
    assert (branches t2 < S n) as H by lia.
    rewrite N1 in Bran; cbn in Bran.
    assert (S (branches t1 + branches t2) < n) as H' by lia.
    change (branches (T t1 t2) < n) in H'.
    destruct (IHn _ H') as [s [? E]].
    exists (T o s). split; cbn; try tauto.
    now rewrite EqAsso, E. 
Qed.


Corollary normalization : forall t, exists t', normal t' /\ Eq t t'.
Proof.
  intros t. apply (pre_normalization ( S(branches t)) ). lia.
Qed.
