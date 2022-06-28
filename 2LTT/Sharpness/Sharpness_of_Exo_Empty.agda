{-# OPTIONS --without-K --exact-split  --two-level --cumulativity #-}

module 2LTT.Sharpness.Sharpness_of_Exo_Empty where

open import 2LTT.Sharpness.isSharp public

---------------------------------------------------------------------------
--⊥ᵉ is sharp
is-⊥ᵉ-Sharp : (k : Level) → isSharp ⊥ᵉ k
is-⊥ᵉ-Sharp k = issharp (⊥ᵉ-is-cofibrant k)
                        ⊥
                        map-⊥ᵉ
                        λ Y → invertibles-are-equiv _ ((λ {star → ind-⊥}) ,
                                                        (λ x → funext λ {x₁ → ex-falso x₁}) ,
                                                        (λ x → refl))
