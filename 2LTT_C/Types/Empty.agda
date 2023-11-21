{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT_C.Types.Empty where

open import 2LTT_C.Primitive


--Empty Type(⊥)
data ⊥ : UU lzero where

ex-falso : {i : Level}{A : UU i} → ⊥ → A
ex-falso ()

ind-⊥ : {i : Level}{P : ⊥ → UU i} → ((x : ⊥) → P x)
ind-⊥ ()


