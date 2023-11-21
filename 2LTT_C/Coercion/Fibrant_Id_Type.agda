{-# OPTIONS --without-K --exact-split --two-level  #-}

module 2LTT_C.Coercion.Fibrant_Id_Type where


open import 2LTT_C.Coercion.Fibrant_Conversion public

--Identity Types for Fibrant Types
Fib-Id : {i : Level} {A : UUᵉ i} {W : isFibrant A} (a b : A) → UU i
Fib-Id {i} {A} {W} a b = Id (ic (Fmap a)) (ic (Fmap b))
  where
  FA : UU i
  FA = isFibrant.fibrant-match W

  Fmap : A → C FA
  Fmap = pr1ᵉ (isFibrant.fibrant-witness W)

----------


