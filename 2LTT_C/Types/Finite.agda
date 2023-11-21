{-# OPTIONS --without-K --exact-split --two-level  #-}

module 2LTT_C.Types.Finite where

open import 2LTT_C.Primitive 
open import 2LTT_C.Types.Coproduct
open import 2LTT_C.Types.Naturals
open import 2LTT_C.Types.Empty
open import 2LTT_C.Types.Unit


----------------------------------------------------------
--Finite types
ℕ< : ℕ → UU lzero
ℕ< zero = ⊥
ℕ< (succ n) = (ℕ< n) + ⊤

