{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT_C.Sharpness.isSharp where

open import 2LTT_C.Cofibration public


--precomposition maps of cofibrant types
precomp : {i j : Level} (A : UUᵉ i) (RA : UU i) (f : A → RA) (Y : RA → UU j)
          → C (Π RA Y) → Πᵉ A (λ a → C (Y (f a)))
precomp {i} {j} A RA f Y (c T) = (λ a → c (T (f a)))
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
                       → Fib-isEquiv {i ⊔ j} {i ⊔ j} {C (Π fibrant-replacement Y)}
                                      {Πᵉ B (λ b → C (Y (fibrant-transfer b)))}
                                      (isfibrant _ ≅-refl)
                                      (isCofibrant-at.Π-fibrant-witness (cofibrant-witness (λ b → (Y (fibrant-transfer b)))))
                                      (precomp B fibrant-replacement fibrant-transfer Y)
