Require Import Lia.

(*
  Right now this formalizes a coding number which can be extended by
  one number at the time. But the Cons1 property really looks like
  something that is close to a prime property. So its conclusion could
  be u ∈ c1 \/ u ∈ c2 given that u ∈ (c1 ++ c2). [++] would then need
  to be an operation which combines two codes to a new code.

  Cons3 can then be changed to: forall n c, exists c', n ∈ (c ++ c').
  Cons2 should maybe be:        forall c c' u, u ∈ c -> u ∈ (c ++ c').
*)

Section Coding.

Variable In : nat -> nat -> Prop.
Variable Nil : nat.
Variable cons : nat -> nat -> nat.

Notation "u ∈ c" := (In u c) (at level 45).
Notation "n ;; c" := (cons n c) (at level 40).

Hypothesis Nil_case   : forall x,       x ∈ Nil     <->  False.
Hypothesis Cons_case  : forall n c x,   x ∈ n ;; c  <->  x = n \/ x ∈ c.
(*
  One can read the Cons_case property as saying
  "either we are in some base case or we enter some recursion"

  I get the feeling that this can therefore be tied more intemitely to
  recursionas the general principle, In the sense that being able to do
  coding is eqivalent to being able to do recursion. This would align
  with what is happening in the Gödel incompleteness proofs. Here one
  needs coding of sequences in order to formulate formulas for (primitive) recursive functions.
 *)

Fact Cons1 n c x :  x ∈ c -> x ∈ n ;; c.
Proof. firstorder. Qed.

Fact Cons2 n c :  n ∈ n ;; c.
Proof. firstorder. Qed.

Hint Resolve Cons1 Cons2 : core.

Fact DN (A : Prop) :        A -> ~~A.                   tauto. Qed.
Fact DN_bind {A B : Prop} : ~~B -> (B -> ~~A) -> ~~A.   tauto. Qed.
Fact lem_ X :               ~~(X \/ ~X).                tauto. Qed.

Ltac ret := apply DN.
Ltac bind H := apply (DN_bind H); clear H; intros H; try tauto.
Ltac lem H := apply (DN_bind (lem_ H)); try tauto.

Lemma coding_bounded p n :
  (forall x, x < n -> p x \/ ~ p x) ->
  exists c, forall u, (u < n -> (p u <-> u ∈ c)) /\ (u ∈ c -> u < n).
Proof.
  assert (forall u n, u < S n -> u < n \/ u = n) as E by lia.
  induction n.
  - intros. exists Nil. intros u.
    split; [lia|]. intros []%Nil_case.
  - intros Dec_p.
    destruct IHn as [c Hc], (Dec_p n ltac:(lia)) as [pn|pn'].
    1, 2: intros; apply Dec_p; lia.
    + exists (n ;; c).
      intros u. split.
      ++ intros [| ->]%E. split.
        * intros p_u%Hc; auto.
        * intros [->|]%Cons_case; auto. now apply Hc.
        * split; eauto.
      ++ intros [->|H%Hc]%Cons_case; auto.
    + exists c.
      intros u; split.
      ++ intros [| ->]%E; [now apply Hc|].
          split; [now intros ?%pn'|].
          intros H%Hc. lia.
      ++ intros H%Hc. lia.
Qed.

Lemma DN_bounded_lem p n :
  ~ ~ (forall x, x < n -> p x \/ ~ p x).
Proof.
  induction n as [|n IH].
  - apply DN. lia.
  - lem (p n). intros Hn.
    bind IH. ret. intros x Hx.
    assert (x < n \/ x = n) as [| ->] by lia.
    all: auto.
Qed.

Corollary DN_coding p n :
  ~~ exists c, forall u, (u < n -> (p u <-> u ∈ c)) /\ (u ∈ c -> u < n).
Proof.
  eapply DN_bind.
  - apply DN_bounded_lem.
  - intro. apply DN, (coding_bounded p n); eauto.
Qed.

Corollary coding_binary p n (b: nat) :
  (forall x, x < n -> p x b \/ ~ p x b) ->
  exists c, forall u, (u < n -> (p u b <-> u ∈ c)) /\ (u ∈ c -> u < n).
Proof.
  apply coding_bounded.
Qed.


End Coding.
