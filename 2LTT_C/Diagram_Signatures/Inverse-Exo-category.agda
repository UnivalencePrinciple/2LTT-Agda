{-# OPTIONS --without-K --exact-split --two-level  #-}

module 2LTT_C.Diagram_Signatures.Inverse-Exo-category where

open import 2LTT_C.Diagram_Signatures.Exo-nat-category public
open import 2LTT_C.Diagram_Signatures.Exo-functor public

--Definition of an inverse exo-category
Inv-Exo-cat : (i j : Level) → UUᵉ (lsuc i ⊔ lsuc j)
Inv-Exo-cat i j = Σᵉ (Exo-cat i j) (λ L → Exo-Functor L op-ℕᵉ-cat)

iexo-cat : {i j : Level} (ℒ : Inv-Exo-cat i j) → (Exo-cat i j)
iexo-cat ℒ = pr1ᵉ ℒ

--rank functor for an inverse exo-category
rk : {i j : Level} (ℒ : Inv-Exo-cat i j) → (Exo-Functor (iexo-cat ℒ) op-ℕᵉ-cat)
rk ℒ = pr2ᵉ ℒ

--finite height inverse exo-categories
has-height : {i j : Level} (ℒ : Inv-Exo-cat i j) (p : ℕᵉ) → UUᵉ i
has-height ℒ p = (a : Objᵉ (iexo-cat ℒ)) → succᵉ ((pr1ᵉ (rk ℒ)) a) ≤ᵉ p

--Type of objects of rank n
_⟅_⟆ : {i j : Level} (ℒ : Inv-Exo-cat i j) (n : ℕᵉ) → UUᵉ i
ℒ ⟅ n ⟆ = Σᵉ (Objᵉ (iexo-cat ℒ)) (λ L →  (pr1ᵉ (rk ℒ) L) =ᵉ n)

ranked-sort : {i j : Level} {ℒ : Inv-Exo-cat i j} {n : ℕᵉ} →
              (L : ℒ ⟅ n ⟆) → (Objᵉ (iexo-cat ℒ))
ranked-sort L = pr1ᵉ L

rank-witness : {i j : Level} {ℒ : Inv-Exo-cat i j} {n : ℕᵉ} →
               (L : ℒ ⟅ n ⟆) → (pr1ᵉ (rk ℒ) (ranked-sort {i} {j} {ℒ} {n} L)) =ᵉ n
rank-witness L = pr2ᵉ L
