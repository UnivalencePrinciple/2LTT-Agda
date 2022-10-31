{-# OPTIONS --without-K --two-level #-}

module 2LTT.Types.List where

open import 2LTT.Primitive

data List {l1 : Level}(A : UU l1) : UU l1  where
  nil : List A
  cons : A → List A → List A

ind-List : {l1 l2 : Level}(A : UU l1) (Y : List {l1} A → UU l2) →
                           Y (nil) → ((a : A) (l : List A) → Y (l) → Y (cons a l)) → ((l : (List A)) → Y l)
ind-List A Y c f nil = c
ind-List A Y c f (cons a l) = f a l (ind-List A Y c f l)

append : {i : Level} {A : UU i} → List A → List A → List A
append nil l'  =  l'
append (cons a l) l' =  cons a (append l l')

embed-to-List : {i : Level} (A : UU i) → A → List A
embed-to-List A a = cons a nil
