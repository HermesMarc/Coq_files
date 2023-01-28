Require Import Lia.

Definition Hardt f n :=
  match n with
  | 0 => 0
  | 1 => 1
  | S (S n) => f (S n) + f(f (S n) - f n)
  end.

Lemma Hardt_is_id f :
  (forall n, Hardt f n = f n) -> forall n, f n = n /\ f(S n) = S n.
Proof.
  intros Hspec. induction n as [| n IH].
  { now rewrite <-!Hspec. }
  destruct n as [|n].
  { rewrite <-!Hspec; cbn.
    now rewrite <-!Hspec. }
  rewrite <-!Hspec.
  destruct IH as [E1 E2].
  split.
  + rewrite <-E2 at 2. apply Hspec.
  + cbn. rewrite !E1, !E2.
    replace (S (S n) - S n) with (1) by lia.
    rewrite <-!Hspec; cbn. lia.
Qed.