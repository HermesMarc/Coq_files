Require Import Arith Lia.

Definition iffT (X Y : Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).


Definition inj {X Y} (f : X -> Y) :=
  forall x x', f x = f x' -> x = x'.
  
Definition inv {X Y} (g : Y -> X) (f : X -> Y) :=
  forall x, g (f x) = x.

Definition bij_pair {X Y} g f :=  @inv X Y g f /\ inv f g.

Definition bijection X Y :=
  { f : X -> Y & { g & bij_pair g f }}.


Lemma size_rect {X} σ f : 
  (forall x, (forall y : X, σ y < σ x -> f y) -> f x) -> forall x, f x.
Proof.
  intros H x. apply H.
  induction (σ x).
  - intros y. now intros F % PeanoNat.Nat.nlt_0_r. 
  - intros y Hy. apply H.
    intros z Hz. apply IHn. lia.
Defined.


Definition fac_spec :=
  fun f => fun n =>
    match n with
      0 => 1
    | S m => n * (f m)
    end.

Fixpoint fac n := fac_spec fac n.



Module AbstractPairing.
  Section abs.
  
  Variable origin : nat * nat.
  Variable next : nat * nat -> nat * nat.
  Hypothesis origin_not_next : forall p, origin <> next p.
  Hypothesis origin_or_next : forall p, {a | p = next a} + {p = origin}.
  Hypothesis inj_next : inj next.

  Fixpoint decode n :=
    match n with
    | 0 => origin
    | S x => next (decode x)
    end.

  Lemma inj_decode : inj decode.
  Proof.
    intros n. induction n; intros []; auto.
    - now intros ?%origin_not_next.
    - now intros ?%eq_sym%origin_not_next.
  Qed.

  Variable code : nat * nat -> nat.
  Hypothesis code_origin : code origin = 0.
  Hypothesis code_next : forall p, code(next p) = S(code p).

  Lemma inv_dc : inv decode code.
  Proof.
    unfold inv.
    apply (size_rect code). intros p rec.
    destruct (origin_or_next p) as [[? ->] | ->].
    - rewrite code_next. cbn. f_equal. apply rec.
      rewrite code_next; auto.
    - now rewrite code_origin.
  Qed.

  Fact inv_cd : inv code decode.
  Proof. 
    intros ?. apply inj_decode. now rewrite inv_dc.
  Qed.

  Corollary Bij : inv code decode /\ inv decode code.
  Proof.
    split. apply inv_cd. apply inv_dc.
  Qed.

  End abs.
End AbstractPairing.



Section Square.

Local Definition next '(x,y) := 
  match x with
  | O => (S y, O)   (* x = 0 : make a diagonal jump *)
  | S x' => if (lt_dec y x)
              then (x , S y)  (* y < x : walk up *)
              else (x', y)    (* y >= x : walk left *)
  end.

Local Definition decode := 
  AbstractPairing.decode (0,0) next.


Fact n00_next : forall p, (0,0) <> next p.
Proof. 
  destruct p as [[ | x'] y]. 
  - discriminate.
  - cbn; destruct (lt_dec y (S x')); try discriminate.
Admitted.

Fact inj_next : inj next.
Proof.
Admitted.

Fact zero_or_next : forall p, {a | p = next a} + {p = (0,0)}.
Proof.
  intros [x y].
  destruct y as [|y'].
  - destruct x as [|x'].
    now right. left; now exists (0, x').
  - destruct (lt_dec (S y') x) as [h|h].
    + left; exists (x, y'). admit.
    + 
Admitted.

Local Definition code '(x,y) := 
    if (lt_dec y x) 
    then x*x + y
    else (S y)*(S y) - (S x).

Fact code_spec1 x y :
  y < x -> code (x,y) = x*x + y.
Proof.
  intros ?; cbn; destruct (lt_dec y x); lia.
Qed.

Fact code_spec2 x y :
  ~ y < x -> code (x,y) = (S y)*(S y) - (S x).
Proof.
  intros ?; cbn; destruct (lt_dec y x); lia.
Qed.

Fact S_lt_S x y : (S x) < (S y) <-> x < y.
Proof. lia. Qed.

Lemma code_next : forall p, code(next p) = S(code p).
Proof.
  intros [x y]; cbn.
  destruct (lt_dec y x), x; cbn; try lia. 
  + destruct (lt_dec (S y) (S x)); nia.
  + destruct (lt_dec y x); lia.
Qed.

Corollary Bij_square : bijection nat (nat * nat).
Proof.
  exists decode, code.
  apply AbstractPairing.Bij.
  - apply n00_next.
  - apply zero_or_next.
  - apply inj_next.
  - reflexivity.
  - apply code_next.
Qed.

End Square.