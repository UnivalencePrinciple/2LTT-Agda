{-# OPTIONS --without-K --two-level  --cumulativity #-}

module 2LTT.Diagram_Signatures.Inverse-Exo-category where

open import 2LTT.Diagram_Signatures.Exo-nat-category public
open import 2LTT.Diagram_Signatures.Exo-functor public

--Definition of an inverse exo-category
Inv-Exo-cat : (i j : Level) → UUᵉ (lsuc i ⊔ lsuc j)
Inv-Exo-cat i j = Σᵉ (Exo-cat i j) (λ L → Exo-Functor L op-ℕᵉ-cat)

--rank functor for an inverse exo-category
rk : {i j : Level} (ℒ : Inv-Exo-cat i j) → (Exo-Functor (pr1ᵉ ℒ) op-ℕᵉ-cat)
rk ℒ = pr2ᵉ ℒ

--finite height inverse exo-categories
has-height : {i j : Level} (ℒ : Inv-Exo-cat i j) (p : ℕᵉ) → UUᵉ i
has-height ℒ p = (a : Objᵉ (pr1ᵉ ℒ)) → succᵉ ((pr1ᵉ (rk ℒ)) a) ≤ᵉ p

--Type of objects of rank n
_⟅_⟆ : {i j : Level} (ℒ : Inv-Exo-cat i j) (n : ℕᵉ) → UUᵉ i
ℒ ⟅ n ⟆ = Σᵉ (Objᵉ (pr1ᵉ ℒ)) (λ L →  (pr1ᵉ (rk ℒ) L) =ᵉ n)
