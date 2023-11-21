{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT_C.Sharpness.Sharpness_of_Finite_Types where


open import 2LTT_C.Sharpness.Sharpness_of_Exo_Empty
open import 2LTT_C.Sharpness.Sharpness_of_Coproduct
open import 2LTT_C.Sharpness.Sharpness_of_Fibrant_Types


--All finite types are sharp
Fin-is-sharp : (n : ℕᵉ) → (j : Level) → isSharp (ℕᵉ< n) j
Fin-is-sharp zeroᵉ = is-⊥ᵉ-Sharp
Fin-is-sharp (succᵉ n) = λ j → +ᵉ-preserve-Sharp (Fin-is-sharp n j) (is-⊤ᵉ-Sharp j)
