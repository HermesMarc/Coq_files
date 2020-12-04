
(* Remark 2.2 on nLab: Lawvere pointed out that ext_surj (he calls it weak surj.) is enough to show the fixpoint theorem *)
(* It turns out, that it even makes the proof the tiniest bit nicer *)
Definition ext_surj {I X Y} (f : I -> (X -> Y)) :=
    forall g, exists i : I, (forall x, g x = f i x).

Definition surj {X Y} f := forall y : Y, exists x : X, f x = y.

Lemma surj_to_extsurj {I X Y : Type} f : surj f -> @ext_surj I X Y f.
Proof.
    intros H g.
    destruct (H g) as [i <-].
    now exists i.
Qed.


Fact Lawvere {X Y} ( f : X -> (X -> Y) ) :
    ext_surj f -> forall g, exists y : Y, g y = y.
Proof.
    intros Hf g.
    destruct (Hf (fun x => g (f x x))) as [a ].
    now exists (f a a).
Qed.


Fact Lawvere' {X Y} (f : X -> (X -> Y) ) :
    surj f -> forall g, exists y : Y, g y = y.
Proof.
    intros Hf%surj_to_extsurj.
    now eapply Lawvere.
Qed.


Fact CP_Lawvere' {X Y} :
    (exists g, forall y : Y, g y <> y) -> 
    forall (f : X -> (X -> Y) ), ~ surj f.
Proof.
    intros [g Hg] f Hf.
    destruct (Lawvere' f Hf g) as [y ].
    now apply (Hg y).
Qed.


Definition Pow X := X -> bool.

Lemma Cantor : ~ exists f : nat -> Pow nat, surj f.
Proof.
    intros [f Hf].
    refine (CP_Lawvere' _ f Hf).
    exists negb. now intros [].
Qed.



Definition weak_representable {I X Y} g (f : I -> (X -> Y)) :=
    exists i : I, forall x : X, f i x = g x.

(* If we are interested in a fixpoint for one paricular function g, only need a representation (up to func-ext) of g (f x x) *)
Lemma Lawvere'' {X Y : Type} g f :
    @weak_representable X X Y (fun x => g (f x x)) f 
    -> exists y, g y = y.
Proof.
    intros [a ]. now exists (f a a).
Qed.


