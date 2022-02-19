{-# OPTIONS --without-K --two-level #-}

module 2LTT.Primitive where

open import Agda.Primitive public

--exo-universe of exotypes
UUᵉ : (i : Level) → SSet (lsuc i)
UUᵉ i = SSet i

--universe of types
UU : (i : Level) → Set (lsuc i)
UU i = Set i
