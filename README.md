Some small projects in Coq I have finished or am still working on.

- [`NumberTheory.v`](/NumberTheory.v) first proofs the [Euclidean division theorem](https://en.wikipedia.org/wiki/Euclidean_division#Division_theorem) and extracts the functions Div and Mod from it. Uniqueness is then shown, as well as the homomorphism properties of the Mod function for addition and multiplictaion. Next, irreducible and prime numbers are defined for which we can proof equivalence and show an informative decider eihter confirming that a number is prime or giving us a decomposition. Using this we can establish that every number has a prime factor and lastly, the infinitude of primes. (TODO: uniqueness of prime decomposition)

- [`CantorPairing.v`](/CantorPairing.v) contains a definition of the standard [Cantor pairing function](https://en.wikipedia.org/wiki/Pairing_function#Cantor_pairing_function) and its inverse, as well as a proof that they are bijections.

- [`Nat_listNat.v`](/Nat_listNat.v) proofs that there is a bijection between the type `nat` and the type `list nat`.

- [`Bij_option.v`](/Bij_option.v) Shows that if `option(X)` and `option(Y)` are in bijection then so are `X` and `Y`. This can then used to show that the definition of finite types with n elements as `option^n(⊥)` is well-behaved.

- [`patties.v`](/patties.v) Contains a formalized solution for a riddle. More details on the riddle can be found in the code.

- [`MinimalLogic.v`](/MinimalLogic.v) first describes a deduction system for [minimal logic](https://en.wikipedia.org/wiki/Minimal_logic) and then establishes implications between LEM, Double Negation Law, Contraposition, Peirce's Law, Explosion and Contradiction, which would all be equivalent in intuitionistic logic. This was developed to go along a [question on stackexchange](https://math.stackexchange.com/questions/3758195/excluded-middle-double-negation-contraposition-and-peirces-law-in-minimal-log).

- [`Drinker.v`](/Drinker.v) has a slight [Drinker paradox](https://en.wikipedia.org/wiki/Drinker_paradox) variation which is shown to be equivalent to LEM.

- [`Lawvere.v`](/Lawvere.v) shows several variations of the [Lawvere fixpoint theorem](https://ncatlab.org/nlab/show/Lawvere's+fixed+point+theorem).

- [`Kaminski.v`](/Kaminski.v) If a type `X` is discrete and every function `f : X -> X` has the property `f(f(f x)) = f x` then `X` can at most have 2 elements.