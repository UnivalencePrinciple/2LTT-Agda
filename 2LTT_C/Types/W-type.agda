{-# OPTIONS --without-K --two-level #-}

module 2LTT_C.Types.W-type where

open import 2LTT_C.Primitive

data WW {l1 l2 : Level}(A : UU l1) (B : A → UU l2) : UU (l1 ⊔ l2)  where
  sup : (a : A) → ((B a → WW A B) → WW A B)

WW-ind : {l1 l2 l3 : Level}(A : UU l1) (B : A → UU l2) (Y : WW {l1} {l2} A B → UU l3) →
                            ((a : A) (f : B (a) → WW {l1} {l2} A B)
                            (h : ((b : B (a)) → Y (f (b)))) → Y (sup a f)) →
                            ((s : WW A B) → Y s)
WW-ind {l1} {l2} {l3} A B Y X (sup a g) = X a g (λ b → WW-ind {l1} {l2} {l3} A B Y X (g b))
