{-# OPTIONS --without-K --two-level --cumulativity #-}

module 2LTT.Exotypes.Vector where

open import 2LTT.Primitive
open import 2LTT.Exotypes.Naturals
open import 2LTT.Exotypes.Sigma
open import 2LTT.Exotypes.Unit
open import 2LTT.Exotypes.Exo_Equality
open import 2LTT.Exotypes.Functions

data Vectorᵉ {i : Level} (A : UUᵉ i) : ℕᵉ → UUᵉ i where
  []ᵉ  : Vectorᵉ A zeroᵉ 
  _∷ᵉ_ : {n : ℕᵉ} → A → Vectorᵉ A n → Vectorᵉ A (succᵉ n)
