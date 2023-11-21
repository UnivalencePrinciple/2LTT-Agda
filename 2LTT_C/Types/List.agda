{-# OPTIONS --without-K --two-level #-}

module 2LTT_C.Types.List where

open import 2LTT_C.Primitive

data List {l1 : Level} (A : UU l1) : UU l1  where
  [] : List A
  _::_ : A → List A → List A

infixr 5 _::_

ind-List : {l1 l2 : Level}(A : UU l1) (Y : List {l1} A → UU l2) →
                           Y ([]) → ((a : A) (l : List A) → Y (l) → Y (a :: l)) → ((l : (List A)) → Y l)
ind-List A Y d f [] = d
ind-List A Y d f (a :: l) = f a l (ind-List A Y d f l)

append : {i : Level} {A : UU i} → List A → List A → List A
append [] l'  =  l'
append (a :: l) l' = a :: (append l l')

embed-to-List : {i : Level} (A : UU i) → A → List A
embed-to-List A a = a :: []
