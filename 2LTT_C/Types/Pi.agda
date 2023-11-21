{-# OPTIONS --without-K --exact-split --two-level  #-}

module 2LTT_C.Types.Pi where

open import 2LTT_C.Primitive 

--------------------------------------------------------
--Type formers of dependent functions for types

Π : {i j : Level} (A : UU i) (P : A → UU j) → UU (i ⊔ j)
Π A P = (x : A) → P x

Π-intro : {i j : Level} (A : UU i) (P : A → UU j) (e : (a : A) → P a) → Π A P
Π-intro A P e = λ x → e x

Π-elim : {i j : Level} {A : UU i} {P : A → UU j} {a : A} → Π A P → P a
Π-elim {a = a} f = f a

