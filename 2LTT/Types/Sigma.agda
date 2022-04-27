{-# OPTIONS --without-K --two-level --cumulativity #-}

module 2LTT.Types.Sigma where

open import 2LTT.Primitive
open import 2LTT.Exotypes.Exo_Equality
open import 2LTT.Exotypes.Sigma


--Type formers of dependent pairs for types
record Σ {i j} (A : UU i) (B : A → UU j) : UU (i ⊔ j) where
  constructor _,_
  field
    pr1 : A
    pr2 : B pr1

open Σ public

infixr 4 _,_

--η-law for Σ type
η-law-Σ : {i j : Level}{A : UU i} {B : A → UU j} → (x : Σ A B) → (x =ᵉ (pr1 x , pr2 x))
η-law-Σ x = reflᵉ

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
exo-dep-pair {i} {j} {A} {B} w w' = Σᵉ {i} {j} (_=ᵉ_ {i} (pr1 w) (pr1 w')) (λ p → (exo-tr B p (pr2 w)) =ᵉ (pr2 w'))

dep-pair-=ᵉ' :  {i j : Level} {A : UU i} {B : A → UU j} (w w' : Σ A B)
             → (exo-dep-pair w w') → w =ᵉ w'
dep-pair-=ᵉ' (a , b) (.a , .b) (reflᵉ , reflᵉ) = reflᵉ

inv-dep-pair-=ᵉ' : {i j : Level} {A : UU i} {B : A → UU j} (w w' : Σ A B)
                    → w =ᵉ w' → (exo-dep-pair w w')
inv-dep-pair-=ᵉ' (a , b) (.a , .b) reflᵉ = reflᵉ , reflᵉ

-------------------------------------------------
--Type formers of products for types
_×_ :  {l1 l2 : Level}(A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
A × B = Σ  A (λ a → B)


×ᵉ-cong' : {i j : Level}{A A' : UU i}{B B' : UU j}
          {p : A =ᵉ A'}{q : B =ᵉ B'}
          → A × B =ᵉ A' × B'
×ᵉ-cong' {p = reflᵉ} {q = reflᵉ} = reflᵉ

exo-pairᵉ' : {i j : Level} {A : UU i} {B : UU j} (x y : A × B)
              → UUᵉ (i ⊔ j)
exo-pairᵉ' x y = ((pr1 x) =ᵉ (pr1 y)) ×ᵉ ((pr2 x) =ᵉ (pr2 y))

pair-=ᵉ' : {i j : Level} {A : UU i} {B : UU j} (x y : A × B)
            → (exo-pairᵉ' x y) → (x =ᵉ y) 
pair-=ᵉ' (a , b) (.a , .b) (reflᵉ , reflᵉ) = reflᵉ

inv-pair-=ᵉ' : {i j : Level} {A : UU i} {B : UU j} (x y : A × B)
                    → x =ᵉ y → (exo-pairᵉ' x y)
inv-pair-=ᵉ' x .x reflᵉ = reflᵉ , reflᵉ

---------------------------------------------------------------------
