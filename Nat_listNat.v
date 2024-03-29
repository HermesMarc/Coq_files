Require Import Arith Lists.List.

Definition injective {X Y} (f : X -> Y) :=
  forall x x', f x = f x' -> x = x'.

Definition inv {X Y} (g : Y -> X) (f : X -> Y) :=
  forall x, g (f x) = x.

Definition bijection X Y :=
  { f : X -> Y & { g & inv g f /\ inv f g }}.

Section Bijection.

  Variable code : nat * nat -> nat.
  Variable decode : nat -> nat * nat.

  Hypothesis decode_code : forall x, decode (code x) = x.
  Hypothesis code_decode : forall x, code (decode x) = x.

  Hypothesis bound : forall x1 x2 n, code (x1, x2) = n -> x2 < S n.
  (* The above hypothesis is easily shown for the Cantor pairing *)

  (* g encodes lists to numbers. We will show that it is a bijection. *)
  Fixpoint g (L : list nat) := 
    match L with
    | nil => 0
    | x::l => S (code (x, g l))
    end.
  
  
  Lemma surj_g : forall N, { L & g L = N }.
  Proof.
    apply (well_founded_induction_type lt_wf); intros [|N] IH.
    - exists nil. reflexivity.
    - rewrite <- (code_decode N).
      destruct (decode N) as [x n] eqn:H.
      destruct (IH n) as [l <-].
      { apply (bound x); congruence. }
      exists (x::l). reflexivity.
  Defined.

  Definition f n := projT1 (surj_g n).  
  (* In the above line, we extracted the candidate inverse f for the function g *)
  (* We will now show that g is injective and verify that f is indeed a left and right-sided inverse *)

  Fact inj_code : injective code.
  Proof.
    intros ? ? ?; rewrite <-decode_code; congruence.
  Defined.
    
  Lemma inj_g : injective g.
  Proof.
    intros A; induction A.
    - intros []. tauto. discriminate.
    - intros [| b B]. discriminate.
      cbn. intros [=H%inj_code]. injection H.
      intros ?%IHA. congruence.
  Defined.


  Fact inv_gf : inv g f.
  Proof.
    intros ?. apply (projT2 (surj_g _)).
  Defined.

  Fact inv_fg : inv f g.
  Proof.
    intros ?. apply inj_g. now rewrite inv_gf.
  Defined.
  

  Corollary Bij_Nat_listNat : bijection nat (list nat).
  Proof.
    exists f, g. split. apply inv_gf. apply inv_fg.
  Defined.
  
End Bijection.