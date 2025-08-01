{-# OPTIONS --without-K --exact-split --two-level --cumulativity #-}

module 2LTT.Types.Naturals where

open import 2LTT.Primitive
open import 2LTT.Types.Unit
open import 2LTT.Types.Sigma
open import 2LTT.Types.Id_Type

--Natural Numbers Type(ℕ)
data ℕ : UU lzero where
     zero : ℕ
     succ : ℕ → ℕ

one = succ zero
two = succ one
three = succ two
four = succ three

--induction principle for ℕ
ind-ℕ : {i : Level} {P : ℕ → UU i} → P zero → ((n : ℕ) → P n → P(succ n)) → ((n : ℕ) → P n)
ind-ℕ P0 PS zero = P0
ind-ℕ P0 PS (succ y) = PS y (ind-ℕ P0 PS y)


--Basic Operations on ℕ
add-ℕ : ℕ → ℕ → ℕ
add-ℕ zero n = n
add-ℕ (succ m) n = succ (add-ℕ m n)

mul-ℕ : ℕ → ℕ → ℕ
mul-ℕ zero n = zero
mul-ℕ (succ m) n = add-ℕ n (mul-ℕ m n)

assoc-add-ℕ : (a b c : ℕ) → Id (add-ℕ (add-ℕ a b) c) (add-ℕ a (add-ℕ b c))
assoc-add-ℕ zero b c = refl
assoc-add-ℕ (succ a) b c = ap succ (assoc-add-ℕ a b c)

add-zero : (m : ℕ) → Id (add-ℕ m zero) m
add-zero zero = refl
add-zero (succ m) = ap succ (add-zero m)

add-succ : (m n : ℕ) → Id (add-ℕ m (succ n)) (succ (add-ℕ m n))
add-succ zero n = refl
add-succ (succ m) n = ap succ (add-succ m n)

comm-add-ℕ : (m n : ℕ) → Id (add-ℕ m n) (add-ℕ n m)
comm-add-ℕ m zero = add-zero m
comm-add-ℕ m (succ n) = (add-succ m n) · (ap succ (comm-add-ℕ m n))


-------------------------------------------------------------
--finite products
folded-× : {i : Level} → ℕ → (A : UU i) → UU i
folded-× zero A = ⊤
folded-× (succ n) A = A × (folded-× n A)

add-folded-× : {i : Level}{A : UU i} → (n m : ℕ) → folded-× n A × folded-× m A → folded-× (add-ℕ n m) A
add-folded-× zero m (x , y) = y
add-folded-× (succ n) m (x , y) = pr1 x , add-folded-× n m (pr2 x , y)

inv-add-folded-× : {i : Level}{A : UU i} → (n m : ℕ) → folded-× (add-ℕ n m) A → folded-× n A × folded-× m A
inv-add-folded-× zero m t = star , t
inv-add-folded-× (succ n) m t = (pr1 t , pr1 (inv-add-folded-× n m (pr2 t))) , pr2 (inv-add-folded-× n m (pr2 t))

add-folded-×-sec : {i : Level}{A : UU i} → (n m : ℕ) → (t : folded-× (add-ℕ n m) A) →
                      Id (add-folded-× n m (inv-add-folded-× n m t)) (t)
add-folded-×-sec zero m t = refl
add-folded-×-sec (succ n) m t = pair⁼ _ _ (refl , add-folded-×-sec n m (pr2 t))

add-folded-×-retr : {i : Level}{A : UU i} → (n m : ℕ) → (t : _×_ {i} {i} (folded-× n A ) (folded-× m A)) →
                      Id (inv-add-folded-× n m (add-folded-× n m t)) (t)
add-folded-×-retr zero m t = refl
add-folded-×-retr {i} (succ n) m t =
  pair⁼ _ _ (pair⁼ _ _ (refl , pr1 (inv-pair⁼ _ _ (add-folded-×-retr n m (pr2 (pr1 t) , pr2 t)))) ,
                            pr2 (inv-pair⁼ _ _ (add-folded-×-retr n m (pr2 (pr1 t) , pr2 t))))
