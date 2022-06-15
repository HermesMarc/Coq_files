Require Import ConstructiveEpsilon.
Module Enum_WO.
Definition Dec {X} (p : X -> Prop) := forall x : X, {p x} + {~p x}.
Definition Enum X := { g & forall x : X, exists n : nat, g n = Some x}.
Definition WO X := forall p : X -> Prop, Dec p -> ex p -> sigT p.
Definition WO_nat := constructive_indefinite_ground_description_nat.
(* Every enumerable type has a witness operator. *)
Lemma lemma X : Enum X -> WO X.
Proof.
  intros [g Hg] p Dec_p H.
  enough (exists n, match g n with Some x => p x | _ => False end) as [n Gn]%WO_nat.
  - destruct (g n); now eauto.
  - intros n. destruct (g n); auto.
  - destruct H as [x ], (Hg x) as [n Hn].
    exists n. now rewrite Hn.
Qed.
End Enum_WO.