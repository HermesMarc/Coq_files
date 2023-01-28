Require Import ConstructiveEpsilon.

Definition DecT {X} (p : X -> Prop) := forall x : X, {p x} + {~p x}.
Definition Cover X Y := { g & forall y : Y, exists x : X, g x = Some y}.
Definition EQ X := forall x y : X, {x = y} + {x <> y}.
Definition WO X := forall p : X -> Prop, DecT p -> ex p -> sigT p.

(* Witness operators transport along coverings *)
Lemma Transport_WO X Y :
  WO X -> Cover X Y -> WO Y.
Proof.
  intros WO_X [g Hg] p Dec_p H.
  enough (exists x, match g x with Some y => p y | _ => False end) as [x Gx]%WO_X.
  - destruct (g x); now eauto.
  - intros x. destruct (g x); auto.
  - destruct H as [x' ], (Hg x') as [x Hx].
    exists x. now rewrite Hx.
Qed.

Lemma Cover_trans X Y Z :
  Cover X Y -> Cover Y Z -> Cover X Z.
Proof.
  intros [f Hf] [g Hg].
  exists (fun x => 
      match f x with 
        | None => None
        | Some y => match g y with
                    | None => None
                    | Some z => Some z
                    end
      end
    ).
  intros z.
  destruct (Hg z) as [y Hy], (Hf y) as [x Hx].
  exists x. now rewrite Hx, Hy.
Qed.



Section Markov.
Definition Dec {X} (p : X -> Prop) := inhabited (DecT p).
Definition pCover1 X Y := exists g, ~~ forall y : Y, exists x : X, g x = Some y.
Definition pCover2 X Y := exists g, forall y : Y, ~~ exists x : X, g x = Some y.
Definition pCover3 X Y := exists g, forall y : Y, exists x : X, ~~ g x = Some y.

Definition pEQ X := ((EQ X -> False) -> False).
Definition Markov X := forall p : X -> Prop, Dec p -> ~~(ex p) -> ex p.
Definition MP := forall f : nat -> nat, ~~(exists n, f n = 0) -> exists n, f n = 0.


Goal forall A B C : Prop, (A -> B \/ C) -> (A /\ ~ C -> B).
Proof. intros; try tauto.


Lemma MP_equiv : MP <-> Markov nat.
Proof.
  split; intros H'.
  - intros p [Dec_p] H.
    pose (f n := if Dec_p n then 0 else 1).
    refine (let Hn := H' f _ in _).
    destruct Hn as [n Hn].
    exists n. revert Hn; unfold f. 
    destruct (Dec_p n); auto. congruence.
  - admit.
Admitted.



Fact Chain_DN {A B : Prop} : ~~A -> ~~(A -> B) -> ~~B. tauto. Qed.
Fact DN {A : Prop} : A -> ~~A. tauto. Qed.



Fact Cover12 X Y : pCover1 X Y -> pCover2 X Y.
Proof.
  intros [g Hg]. exists g. firstorder.
Qed.

Fact Cover32 X Y : pCover3 X Y -> pCover2 X Y.
Proof.
  intros [g Hg]. exists g. firstorder.
Qed.

Lemma Cover21 X Y :
  Markov X -> pEQ Y -> pCover2 X Y -> pCover1 X Y.
Proof.
  intros M_X nneq [g Hg]. exists g.
  intros nH; apply nneq; intros eq; apply nH.
  intros y. refine (M_X _ _ (Hg _)).
  constructor. intros ?; decide equality.
Qed.

Lemma Cover31 X Y :
  pEQ Y -> pCover3 X Y -> pCover1 X Y.
Proof.
  intros nneq [g Hg]. exists g.
  intros nH; apply nneq; intros eq; apply nH.
  intros y. destruct (Hg y) as [x Hx].
  exists x. assert (EQ (option Y)) as eqO.
  - intros ??; decide equality.
  - destruct (eqO (g x)(Some y)); tauto.
Qed.



Lemma Transport_Markov1 X Y :
  Markov X -> pCover1 X Y -> Markov Y.
Proof.
  intros M_X [g nnHg] p [D] nnH.
  enough (~~ exists x, match g x with Some y => p y | _ => False end) as [n Gn]%M_X.
  - destruct (g n); now eauto.
  - constructor. intros n. destruct (g n); auto.
  - apply (Chain_DN nnH), (Chain_DN nnHg), DN.
    intros Hg [x Hx].
    destruct (Hg x) as [n Hn].
    exists n. now rewrite Hn.
Qed.

Lemma Transport_Markov2 X Y :
  Markov X -> pCover2 X Y -> pEQ Y -> Markov Y.
Proof.
  intros. apply (Transport_Markov1 X); auto.
  now apply Cover21.
Qed.
End Markov.