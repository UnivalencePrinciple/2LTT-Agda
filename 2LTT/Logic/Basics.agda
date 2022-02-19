{-# OPTIONS --without-K --two-level #-}

module 2LTT.Logic.Basics where

open import 2LTT.Types

--We already have the definitions of true "⊤", false "⊥".
--We have the definition of being a proposition.
--Here, we'll continue to build Logic in UF.


--Negation
¬_ : {i : Level}(A : UU i) → UU i
¬ A = A → ⊥

--Implication
_⇒_ : {i j : Level}(A : UU i) (B : UU j) → UU (i ⊔ j)
A ⇒ B = A → B

--Conjunction
_∧_ : {i j : Level}(A : UU i)(B : UU j) → UU (i ⊔ j)
A ∧ B = A × B 

--Disjunction
--_∨_ : {i j : Level}(A : UU i)(B : UU j) → UU (i ⊔ j)
--A ∨ B = ∥ A + B ∥

---Universal Quantifier
--∀ (x : A) (P x) is already given by Π A P

--Existensial Quantifier
--∃ : {i j : Level}(A : UU i)(P : A → UU j) → UU (i ⊔ j)
--∃ A P = ∥ Σ A P ∥


