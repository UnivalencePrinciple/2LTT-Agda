{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT_C.Cofibration.Cofibrancy_of_List where


open import 2LTT_C.Cofibration.Cofibrancy_of_Fibrant_Types
open import 2LTT_C.Cofibration.Cofibrancy_of_Sigma
open import 2LTT_C.Cofibration.Properties

folded-×-cofib : {i j : Level} {A : UUᵉ i} → (isCofibrant {i} A (i ⊔ j)) → (n : ℕᵉ) → (isCofibrant (folded-×ᵉ n A) j)
folded-×-cofib {i} {j} P zeroᵉ = ⊤ᵉ-is-cofibrant {i} j
folded-×-cofib {i} {j} P (succᵉ n) = ×ᵉ-preserve-Cofibrant {i} {i} {j} P (folded-×-cofib P n)

tuples-to-list : {i : Level} {A : UUᵉ i} → Σᵉ ℕᵉ (λ n → (folded-×ᵉ n A)) → Listᵉ A
tuples-to-list (zeroᵉ ,ᵉ starᵉ) = []ᵉ
tuples-to-list (succᵉ n ,ᵉ p) = (pr1ᵉ p) ::ᵉ (tuples-to-list (n ,ᵉ (pr2ᵉ p)))

list-to-tuples : {i : Level} {A : UUᵉ i} → Listᵉ A → Σᵉ ℕᵉ (λ n → (folded-×ᵉ n A))
list-to-tuples []ᵉ = (zeroᵉ ,ᵉ starᵉ)
list-to-tuples (a ::ᵉ l) = succᵉ (pr1ᵉ (list-to-tuples l)) ,ᵉ a ,ᵉ pr2ᵉ (list-to-tuples l)

tuples-to-list-has-section : {i : Level} {A : UUᵉ i} → (l : Listᵉ A) →
                       tuples-to-list (list-to-tuples l) =ᵉ l
tuples-to-list-has-section []ᵉ = reflᵉ
tuples-to-list-has-section (x ::ᵉ l) = exo-ap (λ l → x ::ᵉ l) (tuples-to-list-has-section l)

tuples-to-list-has-retraction : {i : Level} {A : UUᵉ i} → (p : Σᵉ {lzero} {i} ℕᵉ (λ n → (folded-×ᵉ n A))) →
                          list-to-tuples (tuples-to-list p) =ᵉ p
tuples-to-list-has-retraction (zeroᵉ ,ᵉ starᵉ) = reflᵉ
tuples-to-list-has-retraction {i} {A} (succᵉ n ,ᵉ a ,ᵉ p) = exo-ap aux-map (tuples-to-list-has-retraction (n ,ᵉ p))
  where
    aux-map : Σᵉ ℕᵉ (λ n₁ → folded-×ᵉ n₁ A) → Σᵉ ℕᵉ (λ n₁ → folded-×ᵉ n₁ A)
    aux-map (k ,ᵉ t) = (succᵉ k ,ᵉ (a ,ᵉ t))

tuples-to-list-iso : {i : Level} {A : UUᵉ i} →  Σᵉ ℕᵉ (λ n → (folded-×ᵉ n A)) ≅ Listᵉ A
tuples-to-list-iso = tuples-to-list ,ᵉ (list-to-tuples ,ᵉ (tuples-to-list-has-retraction  ,ᵉ tuples-to-list-has-section ))

List-isCofibrant : {i j : Level} (A : UUᵉ i) → isCofibrant A (i ⊔ j) → isCofibrant ℕᵉ (i ⊔ j) → isCofibrant (Listᵉ A) j
List-isCofibrant A P Q = isCofibrant-iso tuples-to-list-iso (Σᵉ-preserve-Cofibrant Q (folded-×-cofib P)) 
