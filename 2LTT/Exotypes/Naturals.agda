{-# OPTIONS --without-K --two-level #-}

module 2LTT.Exotypes.Naturals where

open import 2LTT.Primitive
open import 2LTT.Exotypes.Exo_Equality
open import 2LTT.Exotypes.Sigma
open import 2LTT.Exotypes.Functions

--Natural Numbers Exotype(ℕᵉ) 
data ℕᵉ : UUᵉ lzero where
     zeroᵉ : ℕᵉ
     succᵉ : ℕᵉ → ℕᵉ

oneᵉ = succᵉ zeroᵉ
twoᵉ = succᵉ oneᵉ
threeᵉ = succᵉ twoᵉ
fourᵉ = succᵉ threeᵉ
fiveᵉ = succᵉ fourᵉ
sixᵉ = succᵉ fiveᵉ


--induction principle for ℕᵉ
ind-ℕᵉ : {i : Level} {P : ℕᵉ → UUᵉ i} → P zeroᵉ → ((n : ℕᵉ) → P n → P(succᵉ n)) → ((n : ℕᵉ) → P n)
ind-ℕᵉ P0 PS zeroᵉ = P0
ind-ℕᵉ P0 PS (succᵉ y) = PS y (ind-ℕᵉ P0 PS y)

--Successor is injective
succᵉ-is-injective : {m n : ℕᵉ} → (succᵉ m) =ᵉ (succᵉ n) → m =ᵉ n
succᵉ-is-injective reflᵉ = reflᵉ

--Basic Operations on ℕᵉ
add-ℕᵉ : ℕᵉ → ℕᵉ → ℕᵉ
add-ℕᵉ zeroᵉ n = n
add-ℕᵉ (succᵉ m) n = succᵉ (add-ℕᵉ m n)

mul-ℕᵉ : ℕᵉ → ℕᵉ → ℕᵉ
mul-ℕᵉ zeroᵉ n = zeroᵉ
mul-ℕᵉ (succᵉ m) n = add-ℕᵉ n (mul-ℕᵉ m n)

assoc-add-ℕᵉ : (a b c : ℕᵉ) → (add-ℕᵉ (add-ℕᵉ a b) c) =ᵉ (add-ℕᵉ a (add-ℕᵉ b c))
assoc-add-ℕᵉ zeroᵉ b c = reflᵉ
assoc-add-ℕᵉ (succᵉ a) b c = exo-ap succᵉ (assoc-add-ℕᵉ a b c)

add-zeroᵉ : (m : ℕᵉ) → add-ℕᵉ m zeroᵉ =ᵉ m
add-zeroᵉ zeroᵉ = reflᵉ
add-zeroᵉ (succᵉ m) = exo-ap succᵉ (add-zeroᵉ m)

add-succᵉ : (m n : ℕᵉ) → add-ℕᵉ m (succᵉ n) =ᵉ succᵉ (add-ℕᵉ m n)
add-succᵉ zeroᵉ n = reflᵉ
add-succᵉ (succᵉ m) n = exo-ap succᵉ (add-succᵉ m n)

comm-add-ℕᵉ : (m n : ℕᵉ) → add-ℕᵉ m n =ᵉ add-ℕᵉ n m
comm-add-ℕᵉ m zeroᵉ = add-zeroᵉ m
comm-add-ℕᵉ m (succᵉ n) = exo-concat (add-succᵉ m n) (exo-ap succᵉ (comm-add-ℕᵉ m n))

right-injectivity-add-ℕᵉ : (m n k : ℕᵉ) → add-ℕᵉ m n =ᵉ add-ℕᵉ m k → n =ᵉ k
right-injectivity-add-ℕᵉ zeroᵉ n k = idᵉ
right-injectivity-add-ℕᵉ (succᵉ m) n k p = right-injectivity-add-ℕᵉ m n k (succᵉ-is-injective p)

_≤ᵉ_ : ℕᵉ → ℕᵉ → UUᵉ lzero
m ≤ᵉ n = Σᵉ ℕᵉ (λ k → add-ℕᵉ m k =ᵉ n)

all-≤ᵉ-witness-equal : (m n : ℕᵉ) → (p q : m ≤ᵉ n) → p =ᵉ q
all-≤ᵉ-witness-equal m n p q = dep-pair-=ᵉ p q ((right-injectivity-add-ℕᵉ m (pr1ᵉ p) (pr1ᵉ q)
                                                   (exo-concat (pr2ᵉ p) (exo-inv (pr2ᵉ q)))) ,
                                               UIPᵉ _ _)

zero≤ᵉ : (n : ℕᵉ) → zeroᵉ ≤ᵉ n
zero≤ᵉ n = n , reflᵉ

succ≤ᵉ : (m n : ℕᵉ) → m ≤ᵉ n → succᵉ m ≤ᵉ succᵉ n
succ≤ᵉ m n (k , p) = k , exo-ap succᵉ p

≤ᵉ-refl : (n : ℕᵉ) → n ≤ᵉ n
≤ᵉ-refl n = zeroᵉ , (add-zeroᵉ n)

≤ᵉ-trans : {m n k : ℕᵉ} → n ≤ᵉ k → m ≤ᵉ n → m ≤ᵉ k
≤ᵉ-trans {zeroᵉ} {n} {k} _ _ = zero≤ᵉ k
≤ᵉ-trans {succᵉ m} {n} {k} (a , p) (b , q) = (add-ℕᵉ b a) , exo-concat (exo-inv (assoc-add-ℕᵉ (succᵉ m) b a))
                                                                       (exo-concat (exo-ap (λ x → add-ℕᵉ x a) q) p)

{-# INLINE ≤ᵉ-trans #-}

assoc-rule-≤ᵉ : {m n k l : ℕᵉ} → (p : k ≤ᵉ l)(q : n ≤ᵉ k)(r : m ≤ᵉ n) → ≤ᵉ-trans p (≤ᵉ-trans q r) =ᵉ ≤ᵉ-trans (≤ᵉ-trans p q) r
assoc-rule-≤ᵉ {m = m} {l = l} p q r = all-≤ᵉ-witness-equal m l _ _

left-unit-rule-≤ᵉ : {m n : ℕᵉ} → (p : m ≤ᵉ n) → ≤ᵉ-trans (≤ᵉ-refl n) p =ᵉ p
left-unit-rule-≤ᵉ {m} {n} p = all-≤ᵉ-witness-equal m n _ _

right-unit-rule-≤ᵉ : {m n : ℕᵉ} → (p : m ≤ᵉ n) → ≤ᵉ-trans p (≤ᵉ-refl m) =ᵉ p
right-unit-rule-≤ᵉ {m} {n} p = all-≤ᵉ-witness-equal m n _ _
