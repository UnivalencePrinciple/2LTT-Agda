{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT_C.Exotypes.Empty where

open import 2LTT_C.Primitive


--Empty Exotype(⊥ᵉ)
data ⊥ᵉ : UUᵉ lzero where

ex-falsoᵉ : {i : Level}{A : UUᵉ i} → ⊥ᵉ → A
ex-falsoᵉ ()

ind-⊥ᵉ : {i : Level}{P : ⊥ᵉ → UUᵉ i} → ((x : ⊥ᵉ) → P x)
ind-⊥ᵉ ()
