

Class Functor (A B : Type) := mk_Functor
  { f : Type -> Type
  ; fmap : forall a b, (a -> b) -> (f a -> f b)
  }.
Arguments f {_ _} _ _.
Arguments fmap {_ _} _ {_ _} _ _.

Definition Nat {A B} (F G : Functor A B) := forall x, f F x -> f G x.

Definition y {C} (c:C) : Functor C Type.
unshelve refine (mk_Functor _ _ _ _).
- intros x. exact c.
- intros a b f g. cbn in *.
  refine (fun x => f (g x)).
Defined.

Lemma Yoneda C (c : C) F :
  (Nat (y c) F) <-> F c.