Require Import Lia.

Fixpoint fin n : Type :=
  match n with 
    0 => False 
  | S n' => option (fin n') 
  end.

Definition fin2nat {n} (x : fin n) : nat.
Proof.
  induction n as [|n f_n]; [destruct x|].
  destruct x as [y|].
  - refine (S (f_n y)).
  - exact 0.
Defined.

Fact inj_fin2nat {n} (x y : fin n) :
  fin2nat x = fin2nat y -> x = y.
Proof.
  revert x y. induction n. {intros []. }
  intros [x|][y|][=]; try rewrite (IHn x y).
  all: congruence.
Qed.

Fact bound_fin2nat {n} (x : fin n) :
  fin2nat x < n.
Proof.
  revert x. induction n. {intros []. }
  intros [x|].
  - change (S (fin2nat x) < S n).
    specialize (IHn x); lia.
  - cbn; lia.
Qed.

Fixpoint iter {X} (f: X -> X) n x :=
  match n with
  | 0 => x
  | S n => f (iter f n x)
  end.

Fact iter_hom {X f} n m {x:X} :
  iter f (n + m) x = iter f n (iter f m x).
Proof. 
  induction n; [reflexivity|cbn; now f_equal].
Qed.


Section Cycles.

Hypothesis Pigeonhole : forall M N (f : fin M -> fin N),
  M > N -> exists a b, a <> b /\ f a = f b.

Lemma cycle {N} f (x : fin N) :
  exists k c, c + k <= N /\ c > 0 /\ iter f (c + k) x = iter f k x.
Proof.
  destruct N as [|N].
  { destruct x. }
  destruct (Pigeonhole (S (S N)) (S N) 
    (fun n => iter f (fin2nat n) x) ltac:(lia)) as (a&b&H).
  remember (fin2nat a) as n.
  remember (fin2nat b) as m.
  assert (n = m \/ n < m \/ n > m) as [->|[h|h]] by lia.
  {exfalso. apply H. apply inj_fin2nat. congruence. }
  - exists n, (m - n). 
    specialize (bound_fin2nat b) as B.
    repeat split; try lia.
    replace (m - n + n) with m by lia.
    symmetry. apply H.
  - exists m, (n - m).
    specialize (bound_fin2nat a) as B.
    repeat split; try lia.
    replace (n - m + m) with n by lia. 
    apply H.
Qed.

Lemma reduce_once {X} n k m f (x:X) :
  iter f (k + m) x = iter f m x -> m <= n -> iter f (k + n) x = iter f n x.
Proof.
  intros Hm Hmn.
  replace (k + n) with ((n - m) + (k + m)) by lia.
  rewrite iter_hom, Hm, <-iter_hom.
  now replace (n - m + m) with n by lia.
Qed.

Lemma reduce_all {X} n k m d f (x:X) :
  iter f (k + m) x = iter f m x -> m <= n -> iter f (k*d + n) x = iter f n x.
Proof.
  induction d.
  - now replace (k*0 + n) with n by lia.
  - intros H1 H2. cbn.
    replace (k*(S d) + n) with (k + (k*d + n)) by lia.
    rewrite iter_hom, (IHd H1 H2), <-iter_hom.
    eapply reduce_once; eauto.
Qed.

Notation "a \ b" := (exists x, a * x = b) (at level 42).

Lemma Global_Cycling n f (x : fin (S n)) a :
  (forall k, k <= (S n) -> k \ a) -> iter f (a + n) x = iter f n x.
Proof.
  intros Hdiv_a.
  destruct (cycle f x) as (k & c & H1&H2&H3).
  destruct (Hdiv_a c ltac:(lia)) as [d <-].
  eapply reduce_all with k; auto. lia.
Qed.
End Cycles.