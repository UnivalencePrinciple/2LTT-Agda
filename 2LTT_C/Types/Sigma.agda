{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT_C.Types.Sigma where

open import 2LTT_C.Primitive
open import 2LTT_C.Exotypes.Exo_Equality
open import 2LTT_C.Exotypes.Sigma


--Type formers of dependent pairs for types
record Σ {i j} (A : UU i) (B : A → UU j) : UU (i ⊔ j) where
  constructor _,_
  field
    pr1 : A
    pr2 : B pr1

open Σ public

infixr 4 _,_

--induction principle for Σ
ind-Σ : {i j k : Level}{A : UU i} {B : A → UU j} {C : Σ {i} {j} A B → UU k}
         → ((x : A) (y : B x) → C (x , y))
         → ((t : Σ A B) → C t)
ind-Σ f (x , y) = f x y

--currying
curry : {i j k : Level}{A : UU i} {B : A → UU j} {C : Σ {i} {j} A B → UU k}
         → ((t : Σ A B) → C t)
         → ((x : A) (y : B x) → C (x , y))
curry f x y = f (x , y)


exo-dep-pair : {i j : Level} {A : UU i} {B : A → UU j} (w w' : Σ A B)
              → UUᵉ (i ⊔ j)
exo-dep-pair {i} {j} {A} {B} w w' =
  Σᵉ {i} {j} (_=ᵉ_ {i} (c (pr1 w)) (c (pr1 w'))) (λ p → (exo-tr (λ {(c a) → C (B a)}) p (c (pr2 w))) =ᵉ (c (pr2 w')))

dep-pair-=ᵉ' :  {i j : Level} {A : UU i} {B : A → UU j} (w w' : Σ A B)
             → (exo-dep-pair w w') → (c w) =ᵉ (c w')
dep-pair-=ᵉ' (a , b) (.a , .b) (reflᵉ ,ᵉ reflᵉ) = reflᵉ

inv-dep-pair-=ᵉ' : {i j : Level} {A : UU i} {B : A → UU j} (w w' : Σ A B)
                    → (c w) =ᵉ (c w') → (exo-dep-pair w w')
inv-dep-pair-=ᵉ' (a , b) (.a , .b) reflᵉ = reflᵉ ,ᵉ reflᵉ

-------------------------------------------------
--Type formers of products for types
_×_ :  {l1 l2 : Level}(A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
A × B = Σ  A (λ a → B)

exo-pairᵉ' : {i j : Level} {A : UU i} {B : UU j} (x y : A × B)
              → UUᵉ (i ⊔ j)
exo-pairᵉ' x y = ((c (pr1 x)) =ᵉ (c (pr1 y))) ×ᵉ (c ((pr2 x)) =ᵉ (c (pr2 y)))

pair-=ᵉ' : {i j : Level} {A : UU i} {B : UU j} (x y : A × B)
            → (exo-pairᵉ' x y) → ((c x) =ᵉ (c y)) 
pair-=ᵉ' (a , b) (.a , .b) (reflᵉ ,ᵉ reflᵉ) = reflᵉ

inv-pair-=ᵉ' : {i j : Level} {A : UU i} {B : UU j} (x y : A × B)
                    → (c x) =ᵉ (c y) → (exo-pairᵉ' x y)
inv-pair-=ᵉ' x .x reflᵉ = reflᵉ ,ᵉ reflᵉ

---------------------------------------------------------------------
