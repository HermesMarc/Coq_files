Load Preamble.


Definition eq X := fun p : X*X => match p with (x,y) =>  x = y end. 
Definition ap X := fun p : X*X => match p with (x,y) =>  ~~ x = y end. 

Goal forall X, Sdec (eq X) -> Dec (eq X).
Proof.
  intros X [f H]. intros [x y].
  assert (exists n, f n (x, x) = true) as Hn.
  { now apply H. }
  apply WO_nat in Hn. 
  destruct Hn as [n Hn].
  2 : { intros. decide equality. }
  destruct (f n (x,y)) eqn:Hfn.
  - left. apply H. now exists n.
  - right. intros ->. congruence.
Qed. 


Goal forall X, enum (eq X) -> Dec (eq X).
Proof.
  intros X [f H]. intros [x y].
  assert (exists n, f n = Some (x, x)) as Hn.
  { now apply H. }
  apply WO_nat in Hn. 
  destruct Hn as [n Hn].
  2 : { intros. decide equality. }
  destruct (f n) eqn:Hfn.
  - left. apply H. exists n. admit.
  - right. intros ->. congruence.
Admitted. 



Section FixF.

  Variable F : Type.
  Notation "¬ A" := (A -> F) (at level 10).


  Goal forall A B : Prop, (¬A -> ~B) -> ¬ ¬(B -> A).
  Proof.
    intros A B H1 H2.
    apply H2. intros b. exfalso.
    apply H1. intros a. all: tauto.
  Qed.

End FixF.