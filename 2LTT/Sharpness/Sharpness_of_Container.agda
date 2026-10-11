{-# OPTIONS --without-K --exact-split --two-level --cumulativity --type-in-type #-}

module 2LTT.Sharpness.Sharpness_of_Container where

open import 2LTT.Sharpness.isSharp public
open import 2LTT.Sharpness.Properties
open import 2LTT.Sharpness.Sharpness_of_Fibrant_Types
open import 2LTT.Sharpness.Sharpness_of_Sigma
open import 2LTT.Sharpness.Sharpness_of_Product
open import 2LTT.Sharpness.Sharpness_of_Finite_Types
open import 2LTT.Sharpness.On_Sharpness_of_Nat
open import 2LTT.Cofibration.Cofibrancy_of_Container public

--If A is sharp, then so is (ℕᵉ< n → A)
Fin-exp-sharp : {i j : Level} {A : UUᵉ i} → isSharp A (i ⊔ j) → (n : ℕᵉ) → isSharp (ℕᵉ< n → A) j
Fin-exp-sharp {i} {j} P zeroᵉ = isSharp-iso ⊥ᵉ-exp-iso (is-⊤ᵉ-Sharp {i} j)
Fin-exp-sharp {i} {j} P (succᵉ n) = isSharp-iso (succ-exp-iso n) (×ᵉ-preserve-Sharp {i} {i} {j} P (Fin-exp-sharp P n))

--If A is sharp and X is exo-finite, then (X → A) is sharp
finite-exp-sharp : {i j : Level} {X : UUᵉ lzero} {A : UUᵉ i}
                   → isSharp A (i ⊔ j) → Σᵉ ℕᵉ (λ n → ℕᵉ< n ≅ X) → isSharp (X → A) j
finite-exp-sharp P (n ,ᵉ e) = isSharp-iso (Πᵉ-iso-cong' (≅-sym e) (λ _ → ≅-refl)) (Fin-exp-sharp P n)

-----------------------------------------------------------------------------------------

--If A is sharp, each position fiber is exo-finite, and the shape exo-type is sharp,
--then F(A) is sharp.
⟦⟧ᵉ-preserve-Sharp : {i j k : Level} (F : Containerᵉ i lzero) {A : UUᵉ j}
                     → isSharp A (j ⊔ k) → isFinitary F → isSharp (Shape F) (lsuc j ⊔ k)
                     → isSharp (⟦ F ⟧ᵉ A) k
⟦⟧ᵉ-preserve-Sharp {i} {j} {k} (S ◁ P) R fin Q =
  Σᵉ-preserve-Sharp {i} {j} {k} Q (λ s → finite-exp-sharp R (fin s))

--Conversely, if F(⊤ᵉ) is sharp, then the shape exo-type is sharp.
--Hence the hypothesis on the shape exo-type above cannot be weakened.
⟦⟧ᵉ-⊤ᵉ-to-Shape-sharp : {i j : Level} (F : Containerᵉ i lzero)
                       → isSharp {i} (⟦ F ⟧ᵉ (⊤ᵉ {i})) j → isSharp {i} (Shape F) j
⟦⟧ᵉ-⊤ᵉ-to-Shape-sharp {i} {j} F P = isSharp-iso {i} {j} (⟦⟧ᵉ-⊤ᵉ≅Shape F) P

--If ℕᵉ is cofibrant, then all countable exo-types are sharp
Countable-is-sharp : {j : Level} {S : UUᵉ lzero} → isCountable S → isCofibrant ℕᵉ j → isSharp S j
Countable-is-sharp {j} (inlᵉ (n ,ᵉ e)) P = isSharp-iso e (Fin-is-sharp n j)
Countable-is-sharp (inrᵉ e) P = isSharp-iso e (cofib-to-sharp-ℕᵉ P)

--In particular, if ℕᵉ is cofibrant, then F(A) is sharp for every sharp A
--and every finitary container F with countable shapes.
Containerᵉ-isSharp : {i j : Level} (F : Containerᵉ lzero lzero) {A : UUᵉ i}
                     → isSharp A (i ⊔ j) → isFinitary F → isCountable (Shape F) → isCofibrant ℕᵉ (lsuc i ⊔ j)
                     → isSharp (⟦ F ⟧ᵉ A) j
Containerᵉ-isSharp F R fin cnt P = ⟦⟧ᵉ-preserve-Sharp F R fin (Countable-is-sharp cnt P)

--List container
List-Containerᵉ-isSharp : {i j : Level} {A : UUᵉ i}
                          → isSharp A (i ⊔ j) → isCofibrant ℕᵉ (lsuc i ⊔ j)
                          → isSharp (⟦ List-Containerᵉ ⟧ᵉ A) j
List-Containerᵉ-isSharp R P = Containerᵉ-isSharp List-Containerᵉ R List-Containerᵉ-isFinitary List-Containerᵉ-isCountable P

--Hence Listᵉ A is sharp (cf. cofib-list-to-sharp-List)
Listᵉ-isSharp-via-Containerᵉ : {i j : Level} {A : UUᵉ i}
                               → isSharp A (i ⊔ j) → isCofibrant ℕᵉ (lsuc i ⊔ j)
                               → isSharp (Listᵉ A) j
Listᵉ-isSharp-via-Containerᵉ R P = isSharp-iso List-Containerᵉ≅Listᵉ (List-Containerᵉ-isSharp R P)
