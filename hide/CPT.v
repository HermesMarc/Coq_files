


(* (composition f g) is to be read as "first apply f then g"  *)
Definition composition {A B C} (f : A -> B) (g : B -> C) := fun a => g (f a).

Notation "f >> g" := (composition f g) (at level 40).


(* The continuation passing transform *)
Definition CPT {A B} (f : A -> B) := fun {C} (cont : B -> C) => f >> cont.

Check CPT.

Definition id {X} := fun x : X => x. 



Section CPT.

Variables A B C D : Type.
Variable α : A -> B.
Variable β : B -> C.
Variable γ : C -> D.


Fact CPT_asso : CPT (α >> β) γ = CPT α (β >> γ).
Proof. reflexivity. Qed.


Variable a : A.
Variable b : True -> B.

Notation "a`" := (fun f => f a) (at level 2).

Compute CPT (CPT α) a` id. 

End CPT.



Definition Hom {X} P Q := forall x : X, P x -> Q x.

Definition Y {X} (a x : X) := x = a.

Notation "A ≅ B" := ((A -> B) * (B -> A))%type (at level 60).

Lemma Yoneda {X} P (a : X) : P a ≅ Hom (Y a) P.
Proof.
  split.
  - intros P_a. intros x Yax.
    unfold Y in *. now rewrite Yax.
  - intros H. apply H. reflexivity.
Qed.

