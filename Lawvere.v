
Definition surj {X Y} f := forall y : Y, exists x : X, f x = y.

Fact Lawvere {X Y} (f : X -> (X -> Y) ) :
    surj f -> forall g, exists y : Y, g y = y.
Proof.
    intros Hf g.
    destruct (Hf (fun x => g (f x x))) as [a H].
    exists (g(f a a)). pattern (f a) at 2.
    now rewrite H.
Qed.


Fact CP_Lawvere {X Y} (f : X -> (X -> Y) ) :
    (exists g, forall y : Y, g y <> y) -> ~ surj f.
Proof.
    intros [g Hg] Hf.
    destruct (Lawvere f Hf g) as [y ].
    now apply (Hg y).
Qed.