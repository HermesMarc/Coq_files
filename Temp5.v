

Section Monads.
  Variables M1 M2 : Type -> Type.

  Variable ret1 : forall {a}, a -> M1 a.
  Variable bind1 : forall {a b}, (a -> M1 b) -> M1 a -> M1 b.
  Definition join1 {c} := bind1 (fun x: M1 c => x).

  Variable ret2 : forall {a}, a -> M2 a.
  Variable bind2 : forall {a b}, (a -> M2 b) -> M2 a -> M2 b.
  
  Variable swap : forall {a}, M1 (M2 a) -> M2 (M1 a).

  Definition M a := M2 (M1 a).
  Notation "g >> f" := (fun x => f(g x)) (at level 70).

  Goal forall a b, (a -> M b) -> M a -> M b.
  Proof.
    intros a b. unfold M. intros f.
    refine (_ >> bind2 (join1 >> ret2)).
    refine (bind2 (_ >> swap)).
    refine (bind1 (f >> ret1)).
    Show Proof.
Admitted.

End Monads.