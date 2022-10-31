{-# OPTIONS --without-K --exact-split --two-level --cumulativity #-}

module 2LTT.Types.Finite where

open import 2LTT.Primitive 
open import 2LTT.Types.Coproduct
open import 2LTT.Types.Naturals
open import 2LTT.Types.Empty
open import 2LTT.Types.Unit


----------------------------------------------------------
--Finite types
ℕ< : ℕ → UU lzero
ℕ< zero = ⊥
ℕ< (succ n) = (ℕ< n) + ⊤

