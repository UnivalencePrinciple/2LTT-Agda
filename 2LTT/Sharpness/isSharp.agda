{-# OPTIONS --without-K --two-level --cumulativity #-}

module 2LTT.Sharpness.isSharp where

open import 2LTT.Cofibration public
open import 2LTT.Coercion public

--precomposition maps of cofibrant types
precomp : {i j : Level} (A : UUᵉ i) (RA : UU i) (f : A → RA) (Y : RA → UU j)
          → Π RA Y → Πᵉ A (Y ∘ᵉ f)
precomp {i} {j} A RA f Y T = T ∘ᵉ f
{-# INLINE precomp #-}
          

--For exo-type B, being sharp
record isSharp {i : Level} (B : UUᵉ i) (j : Level) : UUᵉ (lsuc (i ⊔ j)) where
  eta-equality
  constructor issharp
  field 
    cofibrant-witness : isCofibrant {i} B j
    fibrant-replacement : UU i
    fibrant-transfer : B → fibrant-replacement
    precomp-is-equiv : (Y : fibrant-replacement → UU j)
                       → Fib-isEquiv {i ⊔ j} {i ⊔ j} {Π fibrant-replacement Y}
                                      {Πᵉ B (Y ∘ᵉ fibrant-transfer)}
                                      (isfibrant _ ≅-refl)
                                      (isCofibrant-at.Π-fibrant-witness (cofibrant-witness (Y ∘ᵉ fibrant-transfer)))
                                      (precomp B fibrant-replacement fibrant-transfer Y)

