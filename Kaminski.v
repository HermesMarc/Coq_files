(* Expressing that X has at most two elements:
  Whenever we have three x y z, then at least one pair is identical *)
Definition most_2 X :=
  forall x y z : X, x = y \/ x = z \/ y = z.

Definition Kaminski X := forall f (x : X), f (f (f x)) = f x.

Definition Eq X := forall x y : X, {x = y} + {~ x = y}.

Goal forall X, Eq X -> Kaminski X -> most_2 X.
Proof.
  intros X eq Kam x1 x2 x3.
  pose (f := fun x =>
  if eq x x1 then x2
  else if eq x x2 then x3 else x1).
  destruct (eq x1 x3), (eq x2 x3); auto.
  left. specialize (Kam f x1). unfold f in *.
  destruct (eq x1 x1), (eq x2 x2), (eq x2 x1), (eq x3 x1), (eq x3 x2); congruence.
Qed.

Goal forall X, most_2 X -> Kaminski X.
Proof.
  intros X H f x.
  specialize (H (f(f x)) (f x) x).
  intuition congruence.
Qed.