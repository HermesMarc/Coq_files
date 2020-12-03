
(* Let's assume we have a Type who behaves similar to nat, and we have a homomorphism from nat to this Type *)

Definition surj {X Y} f := forall y : Y, exists x : X, f x = y.
Definition countable X := exists f, @surj X nat f.

Definition dec P := {P} + {~P}.

Section Tennenbaum.

Variable D : Type.
Variable d0 : D.
Variable dS : D -> D.

Fixpoint ϕ n :  D := 
    match n with
    | 0 => d0
    | S x => dS (ϕ x)
    end.

Definition std x := exists n, ϕ n = x.

(* now assume that ϕ is not surjective and D countable *)
Hypothesis Hnstd : exists e, ~ std e.
Hypothesis Hcount : countable D.


Lemma undec_std : (forall x, dec(std x) ) -> False.
Proof.
    intros H. 
Admitted.



End Tennenbaum.