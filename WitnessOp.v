Load Preamble.

Module WO.
Section WO.
  Variable q : nat -> Prop.
  Variable Dec_q : Dec q.

  Inductive found n : Prop :=
    C : (~ q n -> found (S n)) -> found n.

  Lemma q_found n : q n -> found n.
  Proof.
    intros. now constructor.
  Defined.
  
  Lemma grounded n : found n -> found 0.
  Proof.
    induction n; auto.
    intros. apply IHn. now constructor.
  Defined.

  Lemma foundWitness :
    forall n, found n -> sigT q.
  Proof.
    apply found_rect.
    intros n _ H. destruct (Dec_q n).
    now exists n. now apply H.
  Defined.

  Theorem Witness :
    ex q -> sigT q.
  Proof.
    intros H. apply (foundWitness 0).
    destruct H as [n H]. destruct (Dec_q n).
    - eapply grounded, q_found, H.
    - tauto.
  Defined.
End WO.
End WO.


Section Exmpl.
  Require Import Lia.

  (* Show that x > 12 is decidable *)
  Lemma H1 : Dec (fun x => x > 12).
  Proof.
    intros x; unfold dec.
    destruct (Compare_dec.lt_dec 12 x); auto.
  Defined. 

  (* Proof the proposition that there is a number bigger then 10. Here we use 42 for x. *)
  Example H2 : exists x, x > 12.
  Proof.
    exists 42. lia.
  Defined.

  (* Compute the computational witness that the witness operator now gets, given the proof H2 *)
  
  (*
  Compute projT1 (WO.Witness _ H1 H2). 
  *)
End Exmpl.