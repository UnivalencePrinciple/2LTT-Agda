{-# OPTIONS --without-K --exact-split --two-level  #-}

module 2LTT_C.Coercion.C where

open import 2LTT_C.Exotypes public
open import 2LTT_C.Types public


-----coprodᵉ
map-coprodᵉ : {i j : Level}{A : UU i} {B : UU j} → C A +ᵉ C B → C (A + B)
map-coprodᵉ (inlᵉ (c a)) = c (inl a)
map-coprodᵉ (inrᵉ (c b)) = c (inr b)

-----exo-empty
map-⊥ᵉ : ⊥ᵉ → C ⊥
map-⊥ᵉ = ex-falsoᵉ

-----exo-nat
map-ℕᵉ : ℕᵉ → ℕ
map-ℕᵉ zeroᵉ = zero
map-ℕᵉ (succᵉ x) = succ (map-ℕᵉ x)

-----exo-list
map-Listᵉ : {i : Level}{A : UU i} → Listᵉ (C A) → C (List A)
map-Listᵉ []ᵉ = c []
map-Listᵉ (c a ::ᵉ p) = c (a ::  ic (map-Listᵉ p) )

-----exo-binary-tree
map-BinTreeᵉ : {i j : Level}{N : UU i}{L : UU j} → BinTreeᵉ (C N) (C L) → C (BinTree N L)
map-BinTreeᵉ (leafᵉ (c a)) = c (leaf a)
map-BinTreeᵉ (nodeᵉ p (c a) q) = c (node (ic (map-BinTreeᵉ p)) a (ic (map-BinTreeᵉ q)))

-----exo-equality
map-=ᵉ : {i : Level} {A : UU i} {u v : A} → (c u) =ᵉ (c v) → Id u v
map-=ᵉ reflᵉ = refl

-----exo-universe
map-UUᵉ : {i : Level} → UU i → UUᵉ i
map-UUᵉ {i} A = C A 

-----exo-unit
map-⊤ᵉ : {i : Level} → ⊤ᵉ {i} → C (⊤ {i})
map-⊤ᵉ starᵉ = c star

inv-map-⊤ᵉ : {i : Level} → C (⊤ {i}) → ⊤ᵉ {i}
inv-map-⊤ᵉ (c star) = starᵉ

is-map-⊤ᵉ-iso : {i : Level} → is-exo-iso (map-⊤ᵉ {i}) 
is-map-⊤ᵉ-iso {i} = inv-map-⊤ᵉ {i} ,ᵉ ((λ a → reflᵉ) ,ᵉ (λ b → reflᵉ))

exo-iso-⊤ᵉ : {i : Level} → ⊤ᵉ {i} ≅ C (⊤ {i})
exo-iso-⊤ᵉ = map-⊤ᵉ ,ᵉ is-map-⊤ᵉ-iso

-----exo sigma
map-Σᵉ : {i j : Level}{A : UU i}{B : A → UU j} → Σᵉ (C A) (λ {(c a) → C (B a)}) → C (Σ A B)
map-Σᵉ (c a ,ᵉ c b) = c (a , b)

inv-map-Σᵉ : {i j : Level}{A : UU i}{B : A → UU j} → C (Σ A B) → Σᵉ (C A) (λ {(c a) → C (B a)})
inv-map-Σᵉ (c (a , b)) = c a ,ᵉ c b

is-map-Σᵉ-iso : {i j : Level}{A : UU i}{B : A → UU j} → is-exo-iso (map-Σᵉ {i} {j} {A} {B})
is-map-Σᵉ-iso = inv-map-Σᵉ ,ᵉ ((λ a → reflᵉ) ,ᵉ (λ b → reflᵉ))

exo-Σᵉ-equiv : {i j : Level} {A : UU i}{B : A → UU j} → Σᵉ (C A) (λ {(c a) → C (B a)}) ≅  C (Σ A B)
exo-Σᵉ-equiv = map-Σᵉ ,ᵉ is-map-Σᵉ-iso


-----exo product
map-×ᵉ : {i j : Level}{A : UU i}{B : UU j} → (C A ×ᵉ C B) → C (A × B)
map-×ᵉ (c a ,ᵉ c b) = c (a , b)

inv-map-×ᵉ : {i j : Level}{A : UU i}{B : UU j} → C (A × B) → C A ×ᵉ C B
inv-map-×ᵉ (c (a , b)) = (c a ,ᵉ c b)


-----exo dependent function                                 
map-Πᵉ : {i j : Level} {A : UU i}{B : A → UU j} → Πᵉ (C A) (λ {(c a) → C (B a)}) → C (Π A B)
map-Πᵉ f = c (λ x → ic (f (c x)))

inv-map-Πᵉ : {i j : Level} {A : UU i}{B : A → UU j} → C (Π A B) → Πᵉ (C A) (λ {(c a) → C (B a)}) 
inv-map-Πᵉ (c f) = λ {(c a) → c (f a)}

is-map-Πᵉ-iso : {i j : Level}{A : UU i}{B : A → UU j} → is-exo-iso (map-Πᵉ {i} {j} {A} {B})
is-map-Πᵉ-iso = inv-map-Πᵉ ,ᵉ ((λ a → reflᵉ) ,ᵉ (λ b → reflᵉ))

exo-Πᵉ-equiv : {i j : Level} {A : UU i}{B : A → UU j} → Πᵉ (C A) (λ {(c a) → C (B a)})  ≅ C (Π A B)
exo-Πᵉ-equiv = map-Πᵉ ,ᵉ is-map-Πᵉ-iso
