Definition Dec {X} p := forall x : X , {p x} + {~ p x}. 

Module WO.
Section WO.

  Variable q : nat -> Prop.
  Variable Dec_q : Dec q.

  Inductive T n : Prop :=
    C : (~ q n -> T (S n)) -> T n.


  Lemma grounded n : T n -> T 0.
  Proof.
    induction n; auto.
    intros. apply IHn. now constructor.
  Defined.

  Lemma qT n : q n -> T n.
  Proof.
    intros. now constructor.
  Defined.

  Lemma preWitness : forall n, T n -> {x & q x}.
  Proof.
    apply T_rect.
    intros n _ H. destruct (Dec_q n).
    now exists n. now apply H.
  Defined.

  Theorem Witness : (exists x, q x) -> {x & q x}.
  Proof.
    intros H. apply (preWitness 0).
    destruct H as [n H]. destruct (Dec_q n).
    - eapply grounded, qT, H.
    - tauto.
  Defined. 

End WO.
End WO.



Section Exmpl.

Require Import Lia.

(* Show that x > 10 is decidable *)
Lemma H1 : Dec (fun x => x > 10).
Proof.
  intros x. apply Compare_dec.lt_dec.
Defined. 

(* Proof the proposition that there is a number bigger then 10. Here we use 42 for x. *)
Lemma H2 : exists x, x > 10.
Proof.
  exists 42. lia.
Defined.

(* Compute the computational witness that the witness operator now gets, given the proof H2 *)
Compute projT1 (WO.Witness _ H1 H2).

End Exmpl.