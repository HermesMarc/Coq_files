Require Import Lia Arith.

Fixpoint Σ N := 
  match N with 
  | 0 => 0
  | S n => (Σ n) + (S n)
  end.

Theorem Gauss_Sum : forall N, 2 * Σ N = N*(N + 1).
Proof.
  induction N.
  - cbn. reflexivity.
  - cbn [Σ].
    rewrite Nat.mul_add_distr_l.
    rewrite IHN. lia.
Qed.