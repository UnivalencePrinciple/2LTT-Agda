{-# OPTIONS --without-K --exact-split  --two-level #-}

module 2LTT_C.Exotypes.Naturals where

open import 2LTT_C.Primitive
open import 2LTT_C.Exotypes.Exo_Equality
open import 2LTT_C.Exotypes.Sigma
open import 2LTT_C.Exotypes.Functions
open import 2LTT_C.Exotypes.Unit

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

assoc-add-ℕᵉ : (a b d : ℕᵉ) → (add-ℕᵉ (add-ℕᵉ a b) d) =ᵉ (add-ℕᵉ a (add-ℕᵉ b d))
assoc-add-ℕᵉ zeroᵉ b d = reflᵉ
assoc-add-ℕᵉ (succᵉ a) b d = exo-ap succᵉ (assoc-add-ℕᵉ a b d)

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
                                                   (exo-concat (pr2ᵉ p) (exo-inv (pr2ᵉ q)))) ,ᵉ
                                               UIPᵉ _ _)

zero≤ᵉ : (n : ℕᵉ) → zeroᵉ ≤ᵉ n
zero≤ᵉ n = n ,ᵉ reflᵉ

succ≤ᵉ : (m n : ℕᵉ) → m ≤ᵉ n → succᵉ m ≤ᵉ succᵉ n
succ≤ᵉ m n (k ,ᵉ p) = k ,ᵉ exo-ap succᵉ p

≤ᵉ-refl : (n : ℕᵉ) → n ≤ᵉ n
≤ᵉ-refl n = zeroᵉ ,ᵉ (add-zeroᵉ n)

≤ᵉ-trans : {m n k : ℕᵉ} → n ≤ᵉ k → m ≤ᵉ n → m ≤ᵉ k
≤ᵉ-trans {zeroᵉ} {n} {k} _ _ = zero≤ᵉ k
≤ᵉ-trans {succᵉ m} {n} {k} (a ,ᵉ p) (b ,ᵉ q) = (add-ℕᵉ b a) ,ᵉ exo-concat (exo-inv (assoc-add-ℕᵉ (succᵉ m) b a))
                                                                       (exo-concat (exo-ap (λ x → add-ℕᵉ x a) q) p)

{-# INLINE ≤ᵉ-trans #-}

assoc-rule-≤ᵉ : {m n k l : ℕᵉ} → (p : k ≤ᵉ l)(q : n ≤ᵉ k)(r : m ≤ᵉ n) → ≤ᵉ-trans p (≤ᵉ-trans q r) =ᵉ ≤ᵉ-trans (≤ᵉ-trans p q) r
assoc-rule-≤ᵉ {m = m} {l = l} p q r = all-≤ᵉ-witness-equal m l _ _

left-unit-rule-≤ᵉ : {m n : ℕᵉ} → (p : m ≤ᵉ n) → ≤ᵉ-trans (≤ᵉ-refl n) p =ᵉ p
left-unit-rule-≤ᵉ {m} {n} p = all-≤ᵉ-witness-equal m n _ _

right-unit-rule-≤ᵉ : {m n : ℕᵉ} → (p : m ≤ᵉ n) → ≤ᵉ-trans p (≤ᵉ-refl m) =ᵉ p
right-unit-rule-≤ᵉ {m} {n} p = all-≤ᵉ-witness-equal m n _ _


--strict inequality
_<ᵉ_ : ℕᵉ → ℕᵉ → UUᵉ lzero
m <ᵉ n = succᵉ m ≤ᵉ n

<ᵉ-trans : {m n k : ℕᵉ} → n <ᵉ k → m <ᵉ n → m <ᵉ k
<ᵉ-trans {m} {n} {k} p q = add-ℕᵉ (succᵉ r) s ,ᵉ
                           exo-concat (exo-inv (assoc-add-ℕᵉ (succᵉ m) (succᵉ r) s))
                                      (exo-concat ((exo-ap (λ x → add-ℕᵉ x s)
                                                           (exo-concat (add-succᵉ (succᵉ m) r)
                                                                       (exo-ap succᵉ (pr2ᵉ q)))))
                                                  ((pr2ᵉ p)))
 where
  r = pr1ᵉ q
  s = pr1ᵉ p

--------------------------------------------------
--finite products

folded-×ᵉ : {i : Level} → ℕᵉ → (A : UUᵉ i) → UUᵉ i
folded-×ᵉ {i} zeroᵉ A = ⊤ᵉ {i} 
folded-×ᵉ (succᵉ n) A = A ×ᵉ (folded-×ᵉ n A)

add-folded-×ᵉ : {i : Level}{A : UUᵉ i} → (n m : ℕᵉ) → folded-×ᵉ n A ×ᵉ folded-×ᵉ m A → folded-×ᵉ (add-ℕᵉ n m) A
add-folded-×ᵉ zeroᵉ m (x ,ᵉ y) = y
add-folded-×ᵉ (succᵉ n) m (x ,ᵉ y) = pr1ᵉ x ,ᵉ add-folded-×ᵉ n m (pr2ᵉ x ,ᵉ y)

inv-add-folded-×ᵉ : {i : Level}{A : UUᵉ i} → (n m : ℕᵉ) → folded-×ᵉ (add-ℕᵉ n m) A → folded-×ᵉ n A ×ᵉ folded-×ᵉ m A
inv-add-folded-×ᵉ zeroᵉ m t = starᵉ ,ᵉ t
inv-add-folded-×ᵉ (succᵉ n) m t = (pr1ᵉ t ,ᵉ pr1ᵉ (inv-add-folded-×ᵉ n m (pr2ᵉ t))) ,ᵉ pr2ᵉ (inv-add-folded-×ᵉ n m (pr2ᵉ t))

add-folded-×ᵉ-sec : {i : Level}{A : UUᵉ i} → (n m : ℕᵉ) → (t : folded-×ᵉ (add-ℕᵉ n m) A) →
                      add-folded-×ᵉ n m (inv-add-folded-×ᵉ n m t) =ᵉ t
add-folded-×ᵉ-sec zeroᵉ m t = reflᵉ
add-folded-×ᵉ-sec (succᵉ n) m t = pair-=ᵉ _ _ (reflᵉ ,ᵉ add-folded-×ᵉ-sec n m (pr2ᵉ t))

add-folded-×ᵉ-retr : {i : Level}{A : UUᵉ i} → (n m : ℕᵉ) → (t : _×ᵉ_ {i} {i} (folded-×ᵉ n A ) (folded-×ᵉ m A)) →
                      inv-add-folded-×ᵉ n m (add-folded-×ᵉ n m t) =ᵉ t
add-folded-×ᵉ-retr zeroᵉ m t = reflᵉ
add-folded-×ᵉ-retr {i} (succᵉ n) m t =
  pair-=ᵉ _ _ (pair-=ᵉ _ _ (reflᵉ ,ᵉ pr1ᵉ (inv-pair-=ᵉ _ _ (add-folded-×ᵉ-retr n m (pr2ᵉ (pr1ᵉ t) ,ᵉ pr2ᵉ t)))) ,ᵉ
                            pr2ᵉ (inv-pair-=ᵉ _ _ (add-folded-×ᵉ-retr n m (pr2ᵉ (pr1ᵉ t) ,ᵉ pr2ᵉ t))))


--------------------
suc-level : ℕᵉ → Level → Level
suc-level zeroᵉ i = lsuc i
suc-level (succᵉ n) i = lsuc (suc-level n i)
