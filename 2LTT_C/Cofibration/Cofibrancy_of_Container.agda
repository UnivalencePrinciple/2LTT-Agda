{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT_C.Cofibration.Cofibrancy_of_Container where

open import 2LTT_C.Cofibration.isCofibrant public
open import 2LTT_C.Cofibration.Cofibrancy_of_Fibrant_Types
open import 2LTT_C.Cofibration.Cofibrancy_of_Finite_Types
open import 2LTT_C.Cofibration.Cofibrancy_of_Sigma
open import 2LTT_C.Cofibration.Properties
open import 2LTT_C.Exotypes.Container public

--Exponentials by exo-finite types
⊥ᵉ-exp-iso : {i : Level} {A : UUᵉ i} → ⊤ᵉ {i} ≅ (ℕᵉ< zeroᵉ → A)
⊥ᵉ-exp-iso = (λ _ → ex-falsoᵉ) ,ᵉ
             (λ _ → starᵉ) ,ᵉ
             (λ _ → reflᵉ) ,ᵉ
             (λ h → funextᵉ (λ ()))

succ-exp-iso : {i : Level} {A : UUᵉ i} (n : ℕᵉ) → (A ×ᵉ (ℕᵉ< n → A)) ≅ (ℕᵉ< (succᵉ n) → A)
succ-exp-iso n = (λ { (a ,ᵉ h) (inlᵉ x) → h x ; (a ,ᵉ h) (inrᵉ starᵉ) → a}) ,ᵉ
                 (λ k → k (inrᵉ starᵉ) ,ᵉ (λ x → k (inlᵉ x))) ,ᵉ
                 (λ _ → reflᵉ) ,ᵉ
                 (λ k → funextᵉ (λ { (inlᵉ x) → reflᵉ ; (inrᵉ starᵉ) → reflᵉ}))

--If A is cofibrant, then so is (ℕᵉ< n → A)
Fin-exp-cofib : {i j : Level} {A : UUᵉ i} → isCofibrant {i} A (i ⊔ j) → (n : ℕᵉ) → isCofibrant {i} (ℕᵉ< n → A) j
Fin-exp-cofib {i} {j} P zeroᵉ = isCofibrant-iso ⊥ᵉ-exp-iso (⊤ᵉ-is-cofibrant {i} j)
Fin-exp-cofib {i} {j} P (succᵉ n) = isCofibrant-iso (succ-exp-iso n) (×ᵉ-preserve-Cofibrant {i} {i} {j} P (Fin-exp-cofib {i} {j} P n))

--If A is cofibrant and X is exo-finite, then (X → A) is cofibrant
finite-exp-cofib : {i j : Level} {X : UUᵉ lzero} {A : UUᵉ i}
                   → isCofibrant {i} A (i ⊔ j) → Σᵉ ℕᵉ (λ n → ℕᵉ< n ≅ X) → isCofibrant {i} (X → A) j
finite-exp-cofib {i} {j} P (n ,ᵉ e) = isCofibrant-iso {i} {j} (Πᵉ-iso-cong' (≅-sym e) (λ _ → ≅-refl)) (Fin-exp-cofib {i} {j} P n)

-----------------------------------------------------------------------------------------

--If A is cofibrant, each position fiber is exo-finite, and the shape exo-type is cofibrant,
--then F(A) is cofibrant.
⟦⟧ᵉ-preserve-Cofibrant : {i j k : Level} (F : Containerᵉ i lzero) {A : UUᵉ j}
                         → isCofibrant A (j ⊔ k) → isFinitary F → isCofibrant (Shape F) (j ⊔ k)
                         → isCofibrant (⟦ F ⟧ᵉ A) k
⟦⟧ᵉ-preserve-Cofibrant {i} {j} {k} (S ◁ P) R fin Q =
  Σᵉ-preserve-Cofibrant {i} {j} {k} Q (λ s → finite-exp-cofib R (fin s))

--Conversely, if F(⊤ᵉ) is cofibrant, then the shape exo-type is cofibrant.
--Hence the hypothesis on the shape exo-type above cannot be weakened.
⟦⟧ᵉ-⊤ᵉ-to-Shape-cofib : {i j : Level} (F : Containerᵉ i lzero)
                       → isCofibrant {i} (⟦ F ⟧ᵉ (⊤ᵉ {i})) j → isCofibrant {i} (Shape F) j
⟦⟧ᵉ-⊤ᵉ-to-Shape-cofib {i} {j} F P = isCofibrant-iso {i} {j} (⟦⟧ᵉ-⊤ᵉ≅Shape F) P

--If ℕᵉ is cofibrant, then all countable exo-types are cofibrant
Countable-is-cofibrant : {j : Level} {S : UUᵉ lzero} → isCountable S → isCofibrant ℕᵉ j → isCofibrant S j
Countable-is-cofibrant {j} (inlᵉ (n ,ᵉ e)) P = isCofibrant-iso e (Fin-is-cofibrant n j)
Countable-is-cofibrant (inrᵉ e) P = isCofibrant-iso e P

--In particular, if ℕᵉ is cofibrant, then F(A) is cofibrant for every cofibrant A
--and every finitary container F with countable shapes.
Containerᵉ-isCofibrant : {i j : Level} (F : Containerᵉ lzero lzero) {A : UUᵉ i}
                         → isCofibrant A (i ⊔ j) → isFinitary F → isCountable (Shape F) → isCofibrant ℕᵉ (i ⊔ j)
                         → isCofibrant (⟦ F ⟧ᵉ A) j
Containerᵉ-isCofibrant F R fin cnt P = ⟦⟧ᵉ-preserve-Cofibrant F R fin (Countable-is-cofibrant cnt P)

--List container
List-Containerᵉ-isCofibrant : {i j : Level} {A : UUᵉ i}
                              → isCofibrant A (i ⊔ j) → isCofibrant ℕᵉ (i ⊔ j)
                              → isCofibrant (⟦ List-Containerᵉ ⟧ᵉ A) j
List-Containerᵉ-isCofibrant R P = Containerᵉ-isCofibrant List-Containerᵉ R List-Containerᵉ-isFinitary List-Containerᵉ-isCountable P

--Hence Listᵉ A is cofibrant (cf. List-isCofibrant)
Listᵉ-isCofibrant-via-Containerᵉ : {i j : Level} {A : UUᵉ i}
                                   → isCofibrant A (i ⊔ j) → isCofibrant ℕᵉ (i ⊔ j)
                                   → isCofibrant (Listᵉ A) j
Listᵉ-isCofibrant-via-Containerᵉ R P = isCofibrant-iso List-Containerᵉ≅Listᵉ (List-Containerᵉ-isCofibrant R P)
