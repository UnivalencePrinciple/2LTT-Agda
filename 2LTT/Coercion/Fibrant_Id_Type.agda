{-# OPTIONS --without-K --exact-split --two-level --cumulativity #-}

module 2LTT.Coercion.Fibrant_Id_Type where

open import 2LTT.Exotypes public
open import 2LTT.Types public
open import 2LTT.Coercion.C public
open import 2LTT.Coercion.Fibrant_Conversion public

--Identity Types for Fibrant Types
Fib-Id : {i : Level} {A : UUᵉ i} {W : isFibrant A} (a b : A) → UU i
Fib-Id {i} {A} {W} a b = Id (Fmap a) (Fmap b)
  where
  FA : UU i
  FA = isFibrant.fibrant-match W

  Fmap : A → FA
  Fmap = pr1ᵉ (isFibrant.fibrant-witness W)

----------


