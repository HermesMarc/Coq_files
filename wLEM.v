Load Preamble.

Definition DoubleNegationShift :=
  forall X (p: X -> Prop), (forall x, ~~p x) -> ~~forall x, p x.
Notation DNS := DoubleNegationShift.

Goal ~~LEM <-> DNS.
Proof.
  split; intros H.
  - intros X p h nH.
    DN.remove_dn. apply nH.
    intros x. destruct (H (p x)); firstorder.
  - intros nLEM; unfold DNS in H.
    refine (H _ _ _ nLEM).
    firstorder.
Qed.

Definition wDNS :=
  forall X (p: X -> Prop), ~(forall x, p x) -> ~forall x, ~~p x.

Goal ~~wLEM <-> wDNS.
Proof.
  split; intros H.
  - intros X p nH h.
    DN.remove_dn. apply nH.
    intros x. destruct (H (p x)); firstorder. admit.
  - intros nwLEM; unfold DNS in H.
    unfold wDNS in H. eapply H.
    apply nwLEM. cbn. firstorder.
Admitted.
