{-# OPTIONS --without-K --two-level --cumulativity #-}

module 2LTT.Coercion.C where

open import 2LTT.Exotypes public
open import 2LTT.Types public


C : {i : Level} → (UU i) → (UUᵉ i)
C A = A

c : {i : Level}{A : UU i} → A → C A
c a = a

-----coprodᵉ
map-coprodᵉ : {i j : Level}{A : UU i} {B : UU j} → (C A) +ᵉ (C B) → C (A + B)
map-coprodᵉ (inlᵉ x) = inl x 
map-coprodᵉ (inrᵉ y) = inr y

-----exo-empty
map-⊥ᵉ : ⊥ᵉ → C ⊥
map-⊥ᵉ = ex-falsoᵉ

-----exo-nat
map-ℕᵉ : ℕᵉ → C ℕ
map-ℕᵉ zeroᵉ = zero
map-ℕᵉ (succᵉ x) = succ (map-ℕᵉ x)

-----exo-equality
map-=ᵉ : {i : Level} {A : UU i} {u v : A} → (c u) =ᵉ (c v) → C (Id u v)
map-=ᵉ reflᵉ = refl

-----exo-universe
map-UUᵉ : {i : Level} → C (UU i) → UUᵉ i
map-UUᵉ {i} A = A 

-----exo-unit
map-⊤ᵉ : ⊤ᵉ → C ⊤
map-⊤ᵉ starᵉ = star

inv-map-⊤ᵉ : C ⊤ → ⊤ᵉ
inv-map-⊤ᵉ star = starᵉ

is-map-⊤ᵉ-iso : is-exo-iso map-⊤ᵉ
is-map-⊤ᵉ-iso = inv-map-⊤ᵉ , ((λ a → reflᵉ) , (λ b → reflᵉ))

exo-iso-⊤ᵉ : ⊤ᵉ ≅ C ⊤
exo-iso-⊤ᵉ = map-⊤ᵉ , is-map-⊤ᵉ-iso

-----exo sigma
map-Σᵉ : {i j : Level}{A : UU i}{B : A → UU j} → C {i ⊔ j} (Σ {i} {j} A B) → Σᵉ {i} {j} (C A) (λ x → C (B x))
map-Σᵉ (a , b) = (a , b)

inv-map-Σᵉ : {i j : Level}{A : UU i}{B : A → UU j} → Σᵉ (C A) (λ x → C (B x)) → C (Σ A B)
inv-map-Σᵉ (a , b) = (a , b)

is-map-Σᵉ-iso : {i j : Level}{A : UU i}{B : A → UU j} → is-exo-iso (map-Σᵉ {i} {j} {A} {B})
is-map-Σᵉ-iso = inv-map-Σᵉ , ((λ a → reflᵉ) , (λ b → reflᵉ))

-----exo product
map-×ᵉ : {i j : Level}{A : UU i}{B : UU j} → C (A × B) → (C A) ×ᵉ (C B)
map-×ᵉ (a , b) = (a , b)

inv-map-×ᵉ : {i j : Level}{A : UU i}{B : UU j} → (C A) ×ᵉ (C B) → C (A × B)
inv-map-×ᵉ (a , b) = (a , b)


-----exo dependent function                                 
map-Πᵉ : {i j : Level} {A : UU i}{B : A → UU j} → C (Π A B) → Πᵉ (C A) (λ x → C (B x))
map-Πᵉ f a = f a

inv-map-Πᵉ : {i j : Level} {A : UU i}{B : A → UU j} → Πᵉ (C A) (λ x → C (B x)) → C (Π A B)
inv-map-Πᵉ f = λ a → f a

is-map-Πᵉ-iso : {i j : Level}{A : UU i}{B : A → UU j} → is-exo-iso (map-Πᵉ {i} {j} {A} {B})
is-map-Πᵉ-iso = inv-map-Πᵉ , ((λ a → reflᵉ) , (λ b → reflᵉ))

exo-Πᵉ-equiv : {i j : Level} {A : UU i}{B : A → UU j} → C (Π A B) ≅ Πᵉ (C A) (λ x → C (B x))
exo-Πᵉ-equiv = map-Πᵉ , is-map-Πᵉ-iso

