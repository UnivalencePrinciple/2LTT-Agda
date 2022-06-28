{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT.Exotypes.Finite where

open import 2LTT.Primitive 
open import 2LTT.Exotypes.Coproduct
open import 2LTT.Exotypes.Naturals
open import 2LTT.Exotypes.Empty
open import 2LTT.Exotypes.Unit


--Exo-finite types
ℕᵉ< : ℕᵉ → UUᵉ lzero
ℕᵉ< zeroᵉ = ⊥ᵉ
ℕᵉ< (succᵉ n) = (ℕᵉ< n) +ᵉ ⊤ᵉ



