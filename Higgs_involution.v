(*  This showcases a version of Higg's involution theorem.
    The proof outline was taken from 
      "On Some non-classical extensions of second-order 
       intuitionistic propositional calculus"
    by Andrej Scedrov.
*)
Section Higgs.

Implicit Type p q P : Prop.
Variable f : Prop -> Prop.
Hypothesis f_lc : (forall p q, (f p <-> f q) -> (p <-> q)).
Hypothesis f_eq : (forall p q,  (p <-> q) -> (f p <-> f q)).

Fact L1 P :
  f P -> (f True <-> P).
Proof.
  intros fp. split.
  - intros fT. apply f_lc with True.
    all: tauto.
  - intros p. apply f_eq with P.
    all: tauto.
Qed.

Fact L2 P :
  f (f P) -> P.
Proof.
  intros H%L1. apply (f_lc True P) in H; tauto.
Qed.

Fact L3 P :
  f P -> f (f (f P)).
Proof.
  intros fp.
  apply L1 in fp as H.
  specialize (f_eq (f P) True ltac:(tauto)) as E.
  eapply f_eq with P.
  all: tauto.
Qed.

Theorem Involutive P :
  f (f P) <-> P.
Proof.
  apply f_lc. split.
  - apply L2.
  - apply L3.
Qed.
End Higgs.


Definition PE := forall A B, (A <-> B) -> A = B.

Lemma PE_Involutive (f : Prop -> Prop) :
  PE ->
  (forall p q, (f p <-> f q) -> (p <-> q)) <->
  forall P, f (f P) = P.
Proof.
  intros pe. split.
  - intros f_lc P.
    apply pe, Involutive. try assumption.
    intros A B. now intros ->%pe.
  - intros inv. intros p q H%pe.
    rewrite <-(inv p), <-(inv q).
    now rewrite !H.
Qed.