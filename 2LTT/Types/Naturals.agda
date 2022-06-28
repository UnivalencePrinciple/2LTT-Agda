{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT.Types.Naturals where

open import 2LTT.Primitive

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

