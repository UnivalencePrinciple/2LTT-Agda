{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT_C.Coercion.Fibrant_Functions where

open import 2LTT_C.Coercion.Fibrant_Conversion public

--Fibrancy is preserved under exo-isomorphisms
isFibrant-iso : {i : Level}{A B : UUᵉ i}
              → A ≅ B → isFibrant {i} A
              → isFibrant {i} B
isFibrant-iso {i} I (isfibrant fr fw) = isfibrant fr (≅-trans (≅-sym {i} {i} I) fw)
