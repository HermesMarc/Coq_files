

Definition ext_representable {I X Y} (g : X -> Y) f :=
    exists i : I, forall x : X, f i x = g x.

(* Remark 2.2 on nLab: Lawvere pointed out that surjectivity up to functional extensionality (he calls it weak surj.) is enough to show the fixpoint theorem *)
Definition ext_surj {I X Y} f :=
    forall g, @ext_representable I X Y g f.

Definition surj {X Y} f := forall y : Y, exists x : X, f x = y.


Fact surj_to_extsurj {I X Y : Type} f : surj f -> @ext_surj I X Y f.
Proof.
    intros H g.
    destruct (H g) as [i <-].
    now exists i.
Qed.


Definition diag {X Y} (g : Y -> Y) f := fun x : X => g (f x x).

(* If we are interested in a fixpoint for one particular function g, we only need a representation (up to func-ext) of g (f x x) *)
Fact Lawvere {X Y} g (f : X -> X -> Y) :
    ext_representable (diag g f) f  -> exists y, g y = y.
Proof.
    unfold diag.
    intros [a ]. now exists (f a a).
Qed.


Fact Lawvere' {X Y} (f : X -> X -> Y) :
    ext_surj f -> forall g, exists y : Y, g y = y.
Proof.
    intros Hf g.
    apply (Lawvere g f), Hf.
Qed.


Fact Lawvere'' {X Y} (f : X -> (X -> Y) ) :
    surj f -> forall g, exists y : Y, g y = y.
Proof.
    intros Hf%surj_to_extsurj.
    now eapply Lawvere'.
Qed.


Fact CP_Lawvere'' {X Y} :
    (exists g, forall y : Y, g y <> y) -> 
    forall (f : X -> (X -> Y) ), ~ surj f.
Proof.
    intros [g Hg] f Hf.
    destruct (Lawvere'' f Hf g) as [y ].
    now apply (Hg y).
Qed.


Definition Pow X := X -> bool.

Example Cantor : ~ exists f : nat -> Pow nat, surj f.
Proof.
    intros [f Hf].
    refine (CP_Lawvere'' _ f Hf).
    exists negb. now intros [].
Qed.