{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT_C.Exotypes.Finite where

open import 2LTT_C.Primitive 
open import 2LTT_C.Exotypes.Coproduct
open import 2LTT_C.Exotypes.Naturals
open import 2LTT_C.Exotypes.Empty
open import 2LTT_C.Exotypes.Unit


--Exo-finite types
ℕᵉ< : ℕᵉ → UUᵉ lzero
ℕᵉ< zeroᵉ = ⊥ᵉ
ℕᵉ< (succᵉ n) = (ℕᵉ< n) +ᵉ ⊤ᵉ



