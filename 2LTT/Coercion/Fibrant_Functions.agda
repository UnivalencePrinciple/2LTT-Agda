{-# OPTIONS --without-K --exact-split --two-level --cumulativity #-}

module 2LTT.Coercion.Fibrant_Functions where

open import 2LTT.Exotypes public
open import 2LTT.Types public
open import 2LTT.Coercion.C public
open import 2LTT.Coercion.Fibrant_Conversion public

--Fibrancy is preserved under exo-isomorphisms
isFibrant-iso : {i : Level}{A B : UUᵉ i}
              → A ≅ B → isFibrant {i} A
              → isFibrant {i} B
isFibrant-iso {i} I (isfibrant fr fw) = isfibrant fr (≅-trans (≅-sym {i} {i} I) fw)
