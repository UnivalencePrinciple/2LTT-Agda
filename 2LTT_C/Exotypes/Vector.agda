{-# OPTIONS --without-K --two-level #-}

module 2LTT_C.Exotypes.Vector where

open import 2LTT_C.Primitive
open import 2LTT_C.Exotypes.Naturals
open import 2LTT_C.Exotypes.Sigma
open import 2LTT_C.Exotypes.Unit
open import 2LTT_C.Exotypes.Exo_Equality
open import 2LTT_C.Exotypes.Functions

data Vectorᵉ {i : Level} (A : UUᵉ i) : ℕᵉ → UUᵉ i where
  []ᵉ  : Vectorᵉ A zeroᵉ 
  _∷ᵉ_ : {n : ℕᵉ} → A → Vectorᵉ A n → Vectorᵉ A (succᵉ n)
