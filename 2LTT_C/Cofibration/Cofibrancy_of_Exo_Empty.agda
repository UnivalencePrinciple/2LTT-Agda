{-# OPTIONS --without-K --exact-split --two-level  #-}

module 2LTT_C.Cofibration.Cofibrancy_of_Exo_Empty where

open import 2LTT_C.Coercion.Fibrant_Conversion public
open import 2LTT_C.Coercion.Fibrant_Type_Hierarchy public
open import 2LTT_C.Cofibration.isCofibrant public

⊥ᵉ-is-cofibrant : (k : Level) → isCofibrant ⊥ᵉ k
⊥ᵉ-is-cofibrant = λ k Y → iscofibrant-at
                            (isfibrant
                                ⊤
                                ((λ x → c star) ,ᵉ
                                (λ x x₁ → ex-falsoᵉ x₁) ,ᵉ
                                (λ x → (funextᵉ (λ x₁ → ex-falsoᵉ x₁))),ᵉ
                                (λ x → reflᵉ)))
                            λ K → star , λ {star → refl}
