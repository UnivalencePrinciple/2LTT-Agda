{-# OPTIONS --without-K --exact-split --two-level  #-}

module 2LTT_C.Types.Functions where

open import 2LTT_C.Primitive
open import 2LTT_C.Exotypes.Exo_Equality

--Functions in Universe
id : {i : Level}{A : UU i} → (A → A)
id {A} a = a

infix 30 _∘_
_∘_ : {i j k : Level}
    → {A : UU i} {B : A → UU j} {C : (a : A) → B a → UU k}
    → ({a : A} → (b : B a) → C a b) → (f : (a : A) → B a) → (a : A) → C a (f a)
(g ∘ f) a = g (f a)
{-# INLINE _∘_ #-}

--------------------------------------------------------
