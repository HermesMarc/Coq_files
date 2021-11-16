Definition dec (P : Prop) := sum P (P -> False).
Definition Dec {X} p := forall x : X, dec(p x).

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
  Lemma H1 : Dec (fun x => x > 12).
  Proof.
    intros x; unfold dec.
    destruct (Compare_dec.lt_dec 12 x); auto.
  Defined. 

  (* Proof the proposition that there is a number bigger then 10. Here we use 42 for x. *)
  Lemma H2 : exists x, x > 12.
  Proof.
    exists 42. lia.
  Defined.

  (* Compute the computational witness that the witness operator now gets, given the proof H2 *)
  (*

  Compute projT1 (WO.Witness _ H1 H2). 

  *)
End Exmpl.



Section Enum.

Definition Enum X := 
  { g & forall x : X, exists n : nat, g n = Some x}.
Definition WO X :=
  forall p : X -> Prop, Dec p -> ex p -> sig p.
Definition WO_nat := WO.Witness.


Lemma Enum_WO X : Enum X -> WO X.
Proof.
  intros [g Hg] p D H.
  unshelve refine(
  match
    WO_nat (fun n => match g n with Some x => p x | None => False end) _ _ 
  with existT _ n _ => _ end ).
  - intros n. destruct (g n); [apply D|right; auto].
  - destruct H as [x Hx].
    destruct (Hg x) as [n Hn].
    exists n. now rewrite Hn.
  - destruct (g n); [eauto|tauto].
Qed.

End Enum.