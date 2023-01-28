Load Preamble.
Require Import Arith Lia.
From Coq Require Import PArith.BinPos.


Section Cantor.

Definition Cantor n x y := 2*n = (x+y)*S(x+y) + 2*y.
 
Definition next '(x,y) :=
  match x with
  | 0 => (S y, 0)
  | S x' => (x', S y)
  end.

Lemma decode_spec :
  forall n, Sigma p : nat*nat, let (x,y) := p in Cantor n x y.
Proof.
  unfold Cantor.
  induction n as [|n [p Hp]].
  - exists (0,0); lia.
  - exists (next p).
    destruct p as [[] ]; cbn; lia.
Defined.

Definition decode n := p1 (decode_spec n).
Definition decode_eq n : let (x,y) := decode n in 
  2*n = (x+y)*S(x+y) + 2*y.
Proof. unfold decode. cbn. apply (p2 (decode_spec n)). Admitted.

Fact Gauss n : {k & n*(S n) = 2*k}.
Proof.
  induction n.
  - now exists 0.
  - destruct IHn as [k ].
    exists (n + S k); lia.
Defined.

Lemma code_spec x y : {n & Cantor n x y}.
Proof.
  unfold Cantor.
  destruct (Gauss (x + y)) as [s ].
  exists (s + y); lia.
Defined.

Definition code (p : nat*nat) := let (x,y) := p in p1 (code_spec x y).
Fact code_eq x y : 2*(code (x,y)) = (x+y)*S(x+y) + 2*y.
Proof.
  cbn. destruct (code_spec x y); cbn.
Admitted.

Lemma inv_cd : inv code decode.
Proof.
  intros n.
  enough (2*code (decode n) = 2*n) by lia.
  destruct (decode n) as [x y] eqn:e.
  rewrite code_eq.
  generalize (decode_eq n). now rewrite e.
Qed.

Lemma inv_dc x y :
  decode (code (x,y)) = (x,y).
Proof.
Admitted.

Section Cantor.