{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT_C.Primitive where

open import Agda.Primitive public

--exo-universe of exotypes
UUᵉ : (i : Level) → SSet (lsuc i)
UUᵉ i = SSet i

--universe of types
UU : (i : Level) → Set (lsuc i)
UU i = Set i

--main coercion
record C {i : Level} (A : UU i) : UUᵉ i where
  constructor c
  field ic : A

open C public
