Load Preamble.

(* Here is the most common formulation of Lawvere's Fixpoint theorem:
  If there is a surjection X -> X -> Y, then every function Y -> Y has a fixpoint. *)
Section Lawvere.
  Variables X Y : Type.
  Implicit Type g : Y -> Y.
  Implicit Type f : X -> X -> Y.

  Fact Lawvere_surj f :
    surj f -> forall g, exists y, g y = y.
  Proof.
    intros Surj g.
    destruct (Surj (fun x => g (f x x))) as [a Ha].
    exists (f a a). pattern (f a) at 2.
    now rewrite Ha.
  Qed.
End Lawvere.


(* 
  Remark (2.2) on nLab: Lawvere remarks that surjectivity up to functional extensionality (he calls it weak surj.) is enough to show the fixpoint theorem.

  We additionally want to note that we can generalize from the function type Y -> Y to relations Y -> Y -> Prop. This turns the fixpoint-theorem into a theorem showing the existence of a reflexive element.
*)
Section repr.
  Variables I X Y : Type.
  Implicit Type g : X -> Y -> Prop.

  Definition repr f (i : I) g := 
    forall x : X, g x ((f i) x).

  Definition ext_representable f g :=
    exists i : I, repr f i g.

  Definition ext_surj f :=
    forall g, ext_representable f g.
End repr.
Arguments repr {_ _ _}.
Arguments ext_representable {_ _ _}.
Arguments ext_surj {_ _ _}.


Section Lawvere.

Variables X Y : Type.
Implicit Type R : Y -> Y -> Prop.
Implicit Type f : X -> X -> Y.

Definition diag R f := fun x => R (f x x).

(* If we are interested in a reflexive point for one particular relation R, we only need a representation (up to extensionality) of R (f x x) *)
Fact diag_refl R f :
  forall a, repr f a (diag R f) -> R (f a a) (f a a).
Proof.
  refine (fun a H => H a).
Qed.


Fact Lawvere_diag R f :
  ext_representable f (diag R f) -> exists y, R y y.
Proof.
  intros [a ?%diag_refl]. now exists (f a a).
Qed.


Fact Lawvere f :
  ext_surj f -> forall R, exists y, R y y.
Proof.
  intros Hf R. apply (Lawvere_diag R f), Hf.
Qed.


Fact CP_Lawvere :
  (exists R, forall y, ~ R y y) -> forall f, ~ ext_surj f.
Proof.
  intros [g Hg] f Hf.
  destruct (Lawvere f Hf g) as [y ].
  now apply (Hg y).
Qed.

End Lawvere.



Definition Pow X := X -> bool.
Example Cantor X :
  forall f : X -> Pow X, ~ ext_surj f.
Proof.
  intros f.
  eapply CP_Lawvere.
  exists (fun x y => y = negb x).
  now intros [].
Qed.

Definition Preds X := X -> Prop.
Example Cantor2 X :
  forall f : X -> Preds X, ~ ext_surj f.
Proof.
  intros f.
  eapply CP_Lawvere.
  exists (fun x y => (x <-> ~ y)).
  tauto.
Qed.

Example Negation X :
  ~ exists f : X -> (X -> False), surj f.
Proof.
  intros [f Hf].
  now destruct (Lawvere_surj _ _ _ Hf (fun F => F)) as [[] ].
Qed.