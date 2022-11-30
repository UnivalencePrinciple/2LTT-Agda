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

-----exo-list
map-Listᵉ : {i : Level}{A : UU i} → Listᵉ A → List A
map-Listᵉ []ᵉ = []
map-Listᵉ (x ::ᵉ l) = x :: (map-Listᵉ l)

-----exo-binary-tree
map-BinTreeᵉ : {i j : Level}{N : UU i}{L : UU j} → BinTreeᵉ N L → BinTree N L
map-BinTreeᵉ (leafᵉ x) = leaf x
map-BinTreeᵉ (nodeᵉ t x t₁) = node (map-BinTreeᵉ t) x (map-BinTreeᵉ t₁)

-----exo-equality
map-=ᵉ : {i : Level} {A : UU i} {u v : A} → u =ᵉ v → Id u v
map-=ᵉ reflᵉ = refl

-----exo-universe
map-UUᵉ : {i : Level} → UU i → UUᵉ i
map-UUᵉ {i} A = A 

-----exo-unit
map-⊤ᵉ : {i : Level} → ⊤ᵉ {i} → ⊤ {i}
map-⊤ᵉ starᵉ = star

inv-map-⊤ᵉ : {i : Level} → ⊤ {i} → ⊤ᵉ {i}
inv-map-⊤ᵉ star = starᵉ

is-map-⊤ᵉ-iso : {i : Level} → is-exo-iso (map-⊤ᵉ {i}) 
is-map-⊤ᵉ-iso {i} = inv-map-⊤ᵉ {i} ,ᵉ ((λ a → reflᵉ) ,ᵉ (λ b → reflᵉ))

exo-iso-⊤ᵉ : {i : Level} → ⊤ᵉ {i} ≅ ⊤ {i}
exo-iso-⊤ᵉ = map-⊤ᵉ ,ᵉ is-map-⊤ᵉ-iso

-----exo sigma
map-Σᵉ : {i j : Level}{A : UU i}{B : A → UU j} → Σᵉ A B → Σ A B
map-Σᵉ (a ,ᵉ b) = a , b

inv-map-Σᵉ : {i j : Level}{A : UU i}{B : A → UU j} → Σ A B → Σᵉ A B
inv-map-Σᵉ (a , b) = a ,ᵉ b

is-map-Σᵉ-iso : {i j : Level}{A : UU i}{B : A → UU j} → is-exo-iso (map-Σᵉ {i} {j} {A} {B})
is-map-Σᵉ-iso = inv-map-Σᵉ ,ᵉ ((λ a → reflᵉ) ,ᵉ (λ b → reflᵉ))

exo-Σᵉ-equiv : {i j : Level} {A : UU i}{B : A → UU j} → Σᵉ A B ≅ Σ A B
exo-Σᵉ-equiv = map-Σᵉ ,ᵉ is-map-Σᵉ-iso

-----exo product
map-×ᵉ : {i j : Level}{A : UU i}{B : UU j} → (A ×ᵉ B) → A × B
map-×ᵉ (a ,ᵉ b) = (a , b)

inv-map-×ᵉ : {i j : Level}{A : UU i}{B : UU j} → A × B → A ×ᵉ B
inv-map-×ᵉ (a , b) = (a ,ᵉ b)


-----exo dependent function                                 
map-Πᵉ : {i j : Level} {A : UU i}{B : A → UU j} → Πᵉ A B → Π A B
map-Πᵉ f = f

inv-map-Πᵉ : {i j : Level} {A : UU i}{B : A → UU j} → Π A B → Πᵉ A B
inv-map-Πᵉ f = f

is-map-Πᵉ-iso : {i j : Level}{A : UU i}{B : A → UU j} → is-exo-iso (map-Πᵉ {i} {j} {A} {B})
is-map-Πᵉ-iso = inv-map-Πᵉ ,ᵉ ((λ a → reflᵉ) ,ᵉ (λ b → reflᵉ))

exo-Πᵉ-equiv : {i j : Level} {A : UU i}{B : A → UU j} → Πᵉ A B ≅ Π A B
exo-Πᵉ-equiv = map-Πᵉ ,ᵉ is-map-Πᵉ-iso

