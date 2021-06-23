
Definition repr {I X Y} f (i : I) (g : X -> Y) :=
  forall x : X, (f i) x = g x.

Definition ext_representable {I X Y} (g : X -> Y) f :=
  exists i : I, repr f i g.

(* Remark 2.2 on nLab: Lawvere pointed out that surjectivity up to functional extensionality (he calls it weak surj.) is enough to show the fixpoint theorem *)
Definition ext_surj {I X Y} f :=
  forall g, @ext_representable I X Y g f.

Definition surj {X Y} f := 
  forall y : Y, exists x : X, f x = y.


Fact surj_to_extsurj {I X Y : Type} f : surj f -> @ext_surj I X Y f.
Proof.
  intros H g.
  destruct (H g) as [i <-].
  now exists i.
Qed.


Section Lawvere.

Variables X Y : Type.
Implicit Type g : Y -> Y.
Implicit Type f : X -> X -> Y.

Definition diag g f := fun x => g (f x x).

(* If we are interested in a fixpoint for one particular function g, we only need a representation (up to func-ext) of g (f x x) *)

Fact diag_fix g f :
  forall a, repr f a (diag g f) -> f a a = g (f a a).
Proof.
  refine (fun a H => H a).
Qed.


Fact Lawvere g f :
  ext_representable (diag g f) f  -> exists y, g y = y.
Proof.
  unfold diag. intros [a ]. now exists (f a a).
Qed.


Fact Lawvere_ext_surj f :
    ext_surj f -> forall g, exists y, g y = y.
Proof.
  intros Hf g. apply (Lawvere g f), Hf.
Qed.


Fact Lawvere_surj f :
    surj f -> forall g, exists y, g y = y.
Proof.
  intros Hf%surj_to_extsurj.
  now eapply Lawvere_ext_surj.
Qed.


Fact CP_Lawvere_surj :
    (exists g, forall y, g y <> y) -> 
    forall f, ~ surj f.
Proof.
  intros [g Hg] f Hf.
  destruct (Lawvere_surj f Hf g) as [y ].
  now apply (Hg y).
Qed.

End Lawvere.


Definition Pow X := X -> bool.

Example Cantor X :
  ~ exists f : X -> Pow X, surj f.
Proof.
  intros [f Hf].
  refine (CP_Lawvere_surj _ _ _ f Hf).
  exists negb. now intros [].
Qed.

Example Negation X :
  ~ exists f : X -> (X -> False), surj f.
Proof.
  intros [f Hf].
  refine (CP_Lawvere_surj _ _ _ f Hf).
  exists (fun F => F). now intros [].
Qed.