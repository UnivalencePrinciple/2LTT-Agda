{-# OPTIONS --without-K --exact-split --two-level --cumulativity #-}

module 2LTT.Cofibration.Cofibrancy_of_Finite_Types where

open import 2LTT.Coercion.Fibrant_Conversion public
open import 2LTT.Coercion.Fibrant_Type_Hierarchy public
open import 2LTT.Cofibration.isCofibrant public
open import 2LTT.Cofibration.Cofibrancy_of_Exo_Empty public
open import 2LTT.Cofibration.Cofibrancy_of_Coproduct public
open import 2LTT.Cofibration.Cofibrancy_of_Fibrant_Types public
open import 2LTT.Coercion.Fibrant_Unit public


--All finite types are cofibfant
Fin-is-cofibrant : (n : ℕᵉ) → (j : Level) → isCofibrant (ℕᵉ< n) j
Fin-is-cofibrant zeroᵉ = ⊥ᵉ-is-cofibrant
Fin-is-cofibrant (succᵉ n) = λ j → +ᵉ-preserve-Cofibrant (Fin-is-cofibrant n j) (⊤ᵉ-is-cofibrant j)
