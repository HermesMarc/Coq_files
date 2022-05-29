Some small projects in Coq I have finished or am still working on.

- [`Pigeonhole.v`](/Pigeonhole.v) gives a concise proof of the pigeonhole principle for finite types.

- [`Cycles.v`](/Cycles.v) uses the pigeonhole principle to show that for every finite type `X` with `n` elements, there is a natural number `a` such that for every function `f : X -> X` and `x : X` we have `f^(a + n-1) (x) = f^(n-1)(x)`. In other words: every function reaches a cycle of at most length `a` after only `n-1` iteration steps.

- [`Bij_option.v`](/Bij_option.v) shows that if `option(X)` and `option(Y)` are in bijection then so are `X` and `Y`. This can then used to show that the definition of finite types with n elements as `option^n(⊥)` is well-behaved.

- [`CantorPairing.v`](/CantorPairing.v) contains a definition of the standard [Cantor pairing function](https://en.wikipedia.org/wiki/Pairing_function#Cantor_pairing_function) and its inverse, as well as a proof that they are bijections.

- [`Nat_listNat.v`](/Nat_listNat.v) proofs that there is a bijection between the type `nat` and the type `list nat`.

- [`Enum_WO.v`](/Enum_WO.v) has a short proof which shows that every type that comes with an enumerator also has a witness operator.

- [`NumberTheory.v`](/NumberTheory.v) first proofs the [Euclidean division theorem](https://en.wikipedia.org/wiki/Euclidean_division#Division_theorem) and extracts the functions Div and Mod from it. Uniqueness is then shown, as well as the homomorphism properties of the Mod function. 

- [`MinimalLogic.v`](/MinimalLogic.v) first describes a deduction system for [minimal logic](https://en.wikipedia.org/wiki/Minimal_logic) and then establishes implications between LEM, the double negation law, contraposition, Peirce's Law, the explosion and contradiction principle, which would all be equivalent in intuitionistic logic. This was developed to go along a [question on stackexchange](https://math.stackexchange.com/questions/3758195/excluded-middle-double-negation-contraposition-and-peirces-law-in-minimal-log).

- [`stable_expl.v`](/stable_expl.v) Fixing a formula `F` in minimal logic, one can say that a formula is *`F` explosive* if `F -> ϕ` is provable. The main result of the file is that all formulas are `F` explosive if and only if all atomic formulas are. (i.e. `F` behaves like ⊥ in this case)
For example, in the case of Peano arithmetic: To show that `0 = 1` is explosive, it therefore suffices to show that `0 = 1` implies any other equation `s = t` for some terms `s, t`.

- [`Drinker.v`](/Drinker.v) has a slight variation of [Drinker paradox](https://en.wikipedia.org/wiki/Drinker_paradox) which is shown to be equivalent to LEM.

- [`Lawvere.v`](/Lawvere.v) shows several variations of the [Lawvere fixpoint theorem](https://ncatlab.org/nlab/show/Lawvere's+fixed+point+theorem).

- [`Kaminski.v`](/Kaminski.v) If a type `X` is discrete and every function `f : X -> X` has the property `∀ x, f(f(f x)) = f x` then `X` can at most have 2 elements.

- [`patties.v`](/patties.v) Contains a formalized solution for a riddle. More details on the riddle can be found in the code.
