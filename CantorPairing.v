Require Import Arith Lia.

Definition iffT (X Y : Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).


Definition inj {X Y} (f : X -> Y) :=
  forall x x', f x = f x' -> x = x'.
  
Definition inv {X Y} (g : Y -> X) (f : X -> Y) :=
  forall x, g (f x) = x.

Definition bijection X Y :=
  { f : X -> Y & { g & inv g f /\ inv f g }}.


Lemma size_rect {X} σ f : 
  (forall x, (forall y : X, σ y < σ x -> f y) -> f x) -> forall x, f x.
refine (fun size_rec x => size_rec x
  (nat_rect (fun n => forall y, σ y < n -> f y)
    (fun y Hy0 => ltac:(lia))
    (fun x S_rec y Hyx => size_rec y 
      (fun z Hzy => S_rec z ltac:(lia)))
    (σ x))).
Defined.

Section Cantor.

Definition next '(x,y) := 
  match x with
  | O => (S y, O)
  | S x' => (x', S y)
  end.

Fact n00_next : forall p, (0,0) <> next p.
Proof. destruct p as [[] ]; discriminate. Qed.

Fact inj_next : inj next.
Proof. intros [[] ][[] ]; cbn; congruence. Qed.


Fixpoint decode n := 
  match n with
  | 0 => (0,0)
  | S x => next (decode x)
  end.


Lemma inj_decode : inj decode.
Proof.
  intros n. induction n; intros []; auto.
  - now intros ?%n00_next.
  - now intros ?%eq_sym%n00_next.
  - intros [=?%inj_next%IHn]. congruence.
Qed.

(* show that next is almost surj. *)
Fact zero_or_next : forall p, {a | p = next a} + {p = (0,0)}.
Proof.
  intros [x []].
  - destruct x. now right. left; now exists (0,x).
  - left; now exists (S x, n).
Defined.


Fixpoint Σ n := match n with 0 => 0 | S x => n + Σ x end. 

Definition code '(x,y) := Σ(x+y)+y.

Lemma code_next : forall p, code(next p) = S(code p).
Proof.
  intros [[|x] y]; cbn.
  - rewrite <-!plus_n_O, Nat.add_comm. auto.
  - rewrite !Nat.add_succ_r. cbn. auto.
Qed.

Lemma inv_dc : inv decode code.
Proof.
  unfold inv.
  apply (size_rect code). intros p rec.
  destruct (zero_or_next p) as [[? ->] | ->].
  - rewrite code_next. cbn. f_equal. apply rec.
    rewrite code_next; auto.
  - reflexivity.
Qed.

Fact inv_cd : inv code decode.
Proof.
  intros ?. apply inj_decode. now rewrite inv_dc.
Qed.

Corollary Bij_Nat_NatNat : bijection nat (nat * nat).
Proof.
  exists decode, code. split. apply inv_cd. apply inv_dc.
Qed.

Fact bound x y n : code (x, y) = n -> y < S n.
Proof. cbn. lia. Qed.

Section Cantor.