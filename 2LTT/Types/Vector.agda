{-# OPTIONS --without-K --two-level --cumulativity #-}

module 2LTT.Types.Vector where

open import 2LTT.Primitive
open import 2LTT.Types.Naturals

data Vector {i : Level} (A : UU i) : ℕ → UU i where
  []  : Vector A zero
  _∷_ : {n : ℕ} → A → Vector A n → Vector A (succ n)
