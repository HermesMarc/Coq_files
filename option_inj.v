Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).

Definition inv {X Y: Type} (g: Y -> X) (f: X -> Y) := forall x, g (f x) = x.

Inductive bijection (X Y: Type) : Type :=
| Bijection: forall (f: X -> Y) (g: Y -> X), inv f g -> inv g f -> bijection X Y.

Arguments Bijection {X Y}.

Definition skolem {X Y} (p : X -> Y -> Type) :
  { f & forall x, p x (f x) } <=> forall x, {y & p x y }.
Proof.
  split.
  - intros [f Hf] x. exists (f x). apply Hf.
  - intros F. exists (fun x => projT1 (F x)).
    intros x. exact (projT2 (F x)).
Defined.

Definition rewire {X Y} (f : option X -> option Y) :=
  fun ox =>
  match ox with
  | None => None
  | Some x => match f (Some x) with
              | None => f None
              | Some y => Some y
  end end.

Lemma inv_rewire {X Y} (f : option X -> option Y) g : 
  inv f g -> inv (rewire f) (rewire g).
Proof.
  intros fg. unfold rewire.
  intros [y|]; auto.
  destruct (g (Some y)) as [x|] eqn:g_some; cbn.
  - now rewrite <-g_some, fg.
  - destruct (g None) as [x|] eqn:g_none.
    + rewrite <-g_none, fg. congruence.
    + congruence.
Qed.

Lemma extract {X Y} (f : option X -> option Y) g :
  inv g f -> {F & forall x, rewire f (Some x) = Some (F x) }.
Proof.
  intros gf%inv_rewire.
  apply (skolem (fun x y => rewire f (Some x) = Some y )).
  intros x. destruct (rewire f (Some x)) eqn:f_some.
  - now exists y.
  - enough (Some x = None) by discriminate.
    rewrite <-(gf (Some _)), f_some. reflexivity.
Qed.

Lemma option_inj X Y : 
  bijection (option X) (option Y) -> bijection X Y.
Proof.
  intros [F G FG GF].
  destruct (extract _ _ GF) as [f Hf].
  destruct (extract _ _ FG) as [g Hg].
  refine (Bijection f g _ _).
  - intros y. apply inv_rewire in FG.
    specialize (Hf (g y)). congruence.
  - intros x. apply inv_rewire in GF.
    specialize (Hg (f x)). congruence.
Qed.

(* define finite types with n elements *)
Fixpoint n_type (n : nat) : Type :=
  match n with 0 => False | S n => option (n_type n) end.

Lemma bijection_n_type (n : nat) :
  forall m, bijection (n_type n) (n_type m) -> n = m.
Proof.
  induction n as [|n IHn]; intros [|m]; auto.
  1, 2: intros [f g ]; exfalso.
  - apply g. exact None.
  - apply f. exact None.
  - cbn. now intros <-%option_inj%IHn.
Qed.