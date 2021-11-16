Require Import ConstructiveEpsilon.
Definition Dec {X} (p : X -> Prop) := forall x : X, {p x} + {~p x}.
Definition Enum X := { g & forall x : X, exists n : nat, g n = Some x}.
Definition WO X := forall p : X -> Prop, Dec p -> ex p -> sig p.
Definition WO_nat := constructive_indefinite_ground_description_nat.

(* Every enumerable type has a witness operator. *)
Lemma Enum_WO X : Enum X -> WO X.
Proof.
  intros [g Hg] p D H.
  enough (exists n, match g n with Some x => p x | _ => False end) as HG.
  - apply WO_nat in HG.
    + destruct HG as [n Gn].
      destruct (g n); now eauto.
    + intros n. destruct (g n); auto.
  - destruct H as [x Hx].
    destruct (Hg x) as [n Hn].
    exists n. now rewrite Hn.
Qed.