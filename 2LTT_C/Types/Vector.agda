{-# OPTIONS --without-K --two-level #-}

module 2LTT_C.Types.Vector where

open import 2LTT_C.Primitive
open import 2LTT_C.Types.Naturals

data Vector {i : Level} (A : UU i) : ℕ → UU i where
  []  : Vector A zero
  _∷_ : {n : ℕ} → A → Vector A n → Vector A (succ n)
