{-# OPTIONS --without-K --exact-split --two-level --cumulativity #-}

module 2LTT.Coercion.C where

open import 2LTT.Exotypes public
open import 2LTT.Types public


C : {i : Level} → (UU i) → (UUᵉ i)
C A = A

c : {i : Level}{A : UU i} → A → C A
c a = a

-----coprodᵉ
map-coprodᵉ : {i j : Level}{A : UU i} {B : UU j} → A +ᵉ B → A + B
map-coprodᵉ (inlᵉ x) = inl x 
map-coprodᵉ (inrᵉ y) = inr y

-----exo-empty
map-⊥ᵉ : ⊥ᵉ → ⊥
map-⊥ᵉ = ex-falsoᵉ

-----exo-nat
map-ℕᵉ : ℕᵉ → ℕ
map-ℕᵉ zeroᵉ = zero
map-ℕᵉ (succᵉ x) = succ (map-ℕᵉ x)

-----exo-equality
map-=ᵉ : {i : Level} {A : UU i} {u v : A} → u =ᵉ v → Id u v
map-=ᵉ reflᵉ = refl

-----exo-universe
map-UUᵉ : {i : Level} → UU i → UUᵉ i
map-UUᵉ {i} A = A 

-----exo-unit
map-⊤ᵉ : ⊤ᵉ → ⊤
map-⊤ᵉ starᵉ = star

inv-map-⊤ᵉ : ⊤ → ⊤ᵉ
inv-map-⊤ᵉ star = starᵉ

is-map-⊤ᵉ-iso : is-exo-iso map-⊤ᵉ
is-map-⊤ᵉ-iso = inv-map-⊤ᵉ ,ᵉ ((λ a → reflᵉ) ,ᵉ (λ b → reflᵉ))

exo-iso-⊤ᵉ : ⊤ᵉ ≅ ⊤
exo-iso-⊤ᵉ = map-⊤ᵉ ,ᵉ is-map-⊤ᵉ-iso

-----exo sigma
map-Σᵉ : {i j : Level}{A : UU i}{B : A → UU j} → (Σ {i} {j} A B) → Σᵉ {i} {j} A (λ x → B x)
map-Σᵉ (a , b) = a ,ᵉ b

inv-map-Σᵉ : {i j : Level}{A : UU i}{B : A → UU j} → Σᵉ A (λ x → B x) → Σ A B
inv-map-Σᵉ (a ,ᵉ b) = a , b

is-map-Σᵉ-iso : {i j : Level}{A : UU i}{B : A → UU j} → is-exo-iso (map-Σᵉ {i} {j} {A} {B})
is-map-Σᵉ-iso = inv-map-Σᵉ ,ᵉ ((λ a → reflᵉ) ,ᵉ (λ b → reflᵉ))

-----exo product
map-×ᵉ : {i j : Level}{A : UU i}{B : UU j} → (A × B) → A ×ᵉ B
map-×ᵉ (a , b) = (a ,ᵉ b)

inv-map-×ᵉ : {i j : Level}{A : UU i}{B : UU j} → A ×ᵉ B → A × B
inv-map-×ᵉ (a ,ᵉ b) = (a , b)


-----exo dependent function                                 
map-Πᵉ : {i j : Level} {A : UU i}{B : A → UU j} → Π A B → Πᵉ A (λ x → B x)
map-Πᵉ f a = f a

inv-map-Πᵉ : {i j : Level} {A : UU i}{B : A → UU j} → Πᵉ A (λ x → B x) → Π A B
inv-map-Πᵉ f = λ a → f a

is-map-Πᵉ-iso : {i j : Level}{A : UU i}{B : A → UU j} → is-exo-iso (map-Πᵉ {i} {j} {A} {B})
is-map-Πᵉ-iso = inv-map-Πᵉ ,ᵉ ((λ a → reflᵉ) ,ᵉ (λ b → reflᵉ))

exo-Πᵉ-equiv : {i j : Level} {A : UU i}{B : A → UU j} → Π A B ≅ Πᵉ A (λ x → B x)
exo-Πᵉ-equiv = map-Πᵉ ,ᵉ is-map-Πᵉ-iso

