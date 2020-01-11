Require Import Lia.



Inductive tree : Type :=
  o : tree
| T : tree -> tree -> tree.


Fixpoint branches (t : tree) :=
match t with
  o => 0
| T t1 t2 => 1 + (branches t1) + (branches t2)
end.


Fixpoint normal (T : tree) : Prop :=
match T with
  o => True
| T o t => True /\ (normal t)
| _ => False
end.


Axiom asso : forall t1 t2 t3 : tree, T (T t1 t2) t3 = T t1 (T t2 t3).


Lemma free_leaf : forall t, t <> o -> (exists t', t = T o t').
Proof.
  intros t noLeaf. induction t. exists o. exfalso. apply noLeaf. auto.
  destruct t1.
  - exists t2. auto.
  - assert (T t1_1 t1_2 <> o) as H. discriminate.
    destruct (IHt1 H) as [t' A]. rewrite A. rewrite asso.
    exists (T t' t2). auto.
Qed.


Theorem normalization' : forall (n: nat)(t : tree), 
                       branches t < n -> exists t', normal t'  /\ t = t'.
Proof.
  induction n. destruct t; cbn; lia.
  destruct t; intro Bran. exists o; cbn; auto.
  cbn in Bran. destruct t1.
  - assert (branches t2 < n) as H by lia. destruct (IHn _ H) as [s N].
    exists (T o s). split. cbn; tauto. rewrite (proj2 N); auto.
  - assert (T t1_1 t1_2 <> o) as  Triv by discriminate.
    destruct ( free_leaf (T t1_1 t1_2) Triv ) as [t1 N1].
    rewrite N1. rewrite asso.
    assert (branches t2 < S n) as H by lia.
    rewrite N1 in Bran. cbn in Bran. 
    assert (S (branches t1 + branches t2) < n) as H' by lia.
    change (branches (T t1 t2) < n) in H'. destruct (IHn _ H') as [s N].
    exists (T o s). split; cbn; try tauto. rewrite (proj2 N). auto.
Qed.

Corollary normalization : forall t, exists t', normal t'  /\ t = t'.
Proof.
  intros t. apply (normalization' ( S(branches t)) ). lia.
Qed.





