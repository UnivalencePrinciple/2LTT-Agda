{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT_C.Coercion.Fibrant_Conversion where

open import 2LTT_C.Coercion.C public

----------
--FIBRANT CONVERSION
record isFibrant {i : Level}(B : UUᵉ i) : UUᵉ (lsuc i) where
  constructor isfibrant
  field
    fibrant-match : UU i
    fibrant-witness : B ≅ C (fibrant-match)

open isFibrant public
    
fibrant-conversion : {i : Level} → (B : UUᵉ i) → (isFibrant B) → UU i
fibrant-conversion B (isfibrant fibrant-match fibrant-witness) = fibrant-match

