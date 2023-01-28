

Inductive Lambda : Type :=
  | var : nat -> Lambda
  | lambda : Lambda -> nat -> Lambda
  | app : Lambda -> Lambda -> Lambda.

Notation "$ n" := (var n) (at level 3, format "$ '/' x").
Notation "'λ' n s" := (lambda n s) (at level 50).
Notation "s ; t" := (app s t) (at level 55).
  
Check λ 0 (λ 1 ($0 ; $1)).
