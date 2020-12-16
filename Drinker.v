(* Slightly modified version of the Drinker's Paradox, making it equivalent to XM in the constructive Logic of Coq. *)

Definition XM := forall X, X \/ ~X.
Definition Eater := forall X (p : X -> Prop), 
  X -> exists x : X, (~~p x -> forall x, p x).

Lemma DeMorgan {X} {p : X -> Prop} : XM -> ~(forall x : X, p x) -> exists x, ~p x.
Proof.
Admitted.

Goal XM -> Eater.
Proof.
  intros xm X p x.
  destruct (xm (forall x, p x)) as [|H]; auto.
  - exists x. tauto.
  - apply (DeMorgan xm) in H.
    destruct H as [d ].
    exists d. tauto.
Qed.

Goal Eater -> XM.
Proof.
  intros Eater X.
  specialize (Eater _ (fun x => x \/ ~x) ).
  destruct Eater as [? H]. auto.
  apply H; tauto.
Qed.