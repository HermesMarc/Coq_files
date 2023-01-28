Section refine.

(* refine, fun, leaving blanks  *)

Variables A B C D : Type.


Definition id : A -> A := fun (a : A) => a.

Definition const : A -> (B -> A) :=
  fun (a : A) => (fun (b : B) => a).

Definition ap : A -> ((A -> B) -> B) :=
  fun (a : A) => fun (f : A -> B) => f a.


Goal A -> ((A -> B) -> B).
refine (
  fun (a : A) => fun (f : A -> B) => f a
).
Defined.

(* we can introduce multipe arguments at once
  and even leave out typing if it can be inferred *)
Goal A -> (B -> (C -> (D -> A))).
refine (
  fun (a : A) (b : B) c d => a
).
Defined.

(* We also take the convention that we leave out paratheses on the right of an expression. So the above example is then written *)
Goal A -> B -> C -> D -> A.
refine (
  fun a b c d => a
).
Defined.


Goal ((A -> B) -> C) -> B -> C.
refine (
  fun f b => f (fun a => b) 
).
Defined.


Goal (B -> C) -> (A -> B) -> (A -> C).
refine (
  fun f g a => f (g a)
).
Defined.


Goal ((((A -> B) -> A) -> A) -> B) -> B.
refine (
  fun f => f (fun g => 
  g (fun a => f (fun h => a)))
).
Defined.


Goal (A -> (B -> C)) -> ((A -> B) -> (A -> C)).
refine (
  fun f g a => f a (g a)
).
Defined.


End refine.





Section Products.

(* Product Types, pair construction, pair destruction*)

Variables A B C D : Type.


Goal A -> B -> A * B.
refine (
  fun a b => pair a b
).
Defined.


Goal A * B -> A.
refine (
  fun p => match p with
          | pair a b => a
          end 
).
Defined.


Goal (A -> B) * (B -> C) -> (A -> C).
refine (
  fun p => match p with 
          | pair f g => (fun a => g (f a))
          end
).
Defined.

Goal (A * B -> C) -> (A -> B -> C).
refine (
  fun f a b => f (pair a b)
).
Defined.

Goal (A -> B -> C) -> (A * B -> C).
refine (
  fun f p => match p with
            | pair a b => f a b
            end
).
Defined. 

(* We can now express that there are functions going into both directions between 2 types A and B, by showing that there is a pair of type *)
Goal (A -> B) * (B -> A).
Admitted.



End Products. 




Section Tactics.

(* intros, apply, exact *)

Variables A B C D : Type.

Goal A -> A.
  intros a. exact a.
Defined.


Goal (A -> (B -> A)).
 intros a b. exact a.
Defined.


Goal (B -> C) -> (A -> B) -> (A -> C).
  intros f g a.
  apply f. apply g. exact a.
Defined.


Goal ((((A -> B) -> A) -> A) -> B) -> B.
  intros f. apply f.
  intros g. apply g.
  intros a. apply f.
  intros h. exact a.
Defined.


Goal (A -> (B -> C)) -> (A -> B) -> (A -> C).
refine (
  fun f g a => f a (g a)
).
Defined.


End Tactics.