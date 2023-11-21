{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT_C.Sharpness.Sharpness_of_Exo_Empty where

open import 2LTT_C.Sharpness.isSharp public

---------------------------------------------------------------------------
--⊥ᵉ is sharp
is-⊥ᵉ-Sharp : (k : Level) → isSharp ⊥ᵉ k
is-⊥ᵉ-Sharp k = issharp (⊥ᵉ-is-cofibrant k)
                        ⊥
                        (λ x → ic (ex-falsoᵉ x))
                        λ Y → invertibles-are-equiv _ ((λ {star → ind-⊥}) ,
                                                        (λ x → funext λ {x₁ → ex-falso x₁}) ,
                                                        (λ x → refl))
