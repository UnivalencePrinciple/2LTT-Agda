{-# OPTIONS --without-K --exact-split --two-level --cumulativity #-}

module 2LTT.Coercion.Fibrant_Unit where

open import 2LTT.Exotypes public
open import 2LTT.Types public
open import 2LTT.Coercion.C public
open import 2LTT.Coercion.Fibrant_Conversion public


--⊤ᵉ is fibrant
isFibrant-⊤ᵉ : {i : Level} → isFibrant (⊤ᵉ {i})
isFibrant-⊤ᵉ {i} = isfibrant {i} ⊤ (exo-iso-⊤ᵉ {i})
