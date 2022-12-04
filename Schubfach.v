Require Import Lia Lists.List.
Import ListNotations.
Notation "x 'el' A" := (In x A) (at level 70).

Fixpoint sum L : nat :=
  match L with
    nil => 0
  | x :: l => x + sum l
  end.

Ltac resolve := repeat split; tauto || nia.
  
(*  Gives an upper bound for the sum of a list. 
 *)
Lemma upper_bound L :
  L <> nil -> exists n, n el L /\ sum L <= n*(length L).
Proof.
  induction L as [|n l]; cbn; [tauto|].
  intros _. destruct l as [|m l].
  - exists n; cbn. resolve.
  - destruct IHl as [x Hx]; try discriminate.
    destruct (n - x) eqn:?.
    + exists x. resolve.
    + exists n. resolve.
Qed.

(*  A derived statement which shows that when more then M items
    are distributed over N bins, there is at least one bin with
    more than floor(N/M) items.
 *)
Lemma pigeon_hole_nat M L :
  sum L > M -> exists x, x el L /\ x*(length L) > M.
Proof.
  intros ?.
  destruct (upper_bound L) as [n Hn].
  destruct L as [|x l]; cbn in *; discriminate || lia.
  exists n. resolve.
Qed.

Lemma lower_bound L :
  L <> nil -> exists n, n el L /\ sum L >= n*(length L).
Proof.
  induction L as [|n l]; cbn; [tauto|].
  intros _. destruct l as [|m l].
  - exists n; cbn. resolve.
  - destruct IHl as [x Hx]; try discriminate.
    destruct (n - x) eqn:?.
    + exists x. resolve.
    + exists n. resolve.
Qed.

Lemma co_pigeon_hole_nat M L :
  sum L <= M -> exists x, x el L /\ x*(length L) <= M.
Proof.
  intros ?.
  destruct (lower_bound L) as [n Hn].
  destruct L as [|x l]; cbn in *; try discriminate. admit.
  exists n. resolve.
Admitted.
