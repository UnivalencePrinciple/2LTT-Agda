{-# OPTIONS --without-K --two-level  #-}

module 2LTT.Exotypes.Sigma where

open import 2LTT.Primitive
open import 2LTT.Exotypes.Exo_Equality


--Type formers of dependent pairs for exotypes
record Σᵉ {i j} (A : UUᵉ i) (B : A → UUᵉ j) : UUᵉ (i ⊔ j) where
  constructor _,_
  field
    pr1ᵉ : A
    pr2ᵉ : B pr1ᵉ

open Σᵉ public

infixr 4 _,_

--η-law for Σᵉ type
η-law-Σᵉ : {i j : Level}{A : UUᵉ i} {B : A → UUᵉ j} → (x : Σᵉ A B) → (x =ₛᵉ (pr1ᵉ x , pr2ᵉ x))
η-law-Σᵉ x = reflₛᵉ

--induction principle for Σᵉ
ind-Σᵉ : {i j k : Level}{A : UUᵉ i} {B : A → UUᵉ j} {C : Σᵉ A B → UUᵉ k}
         → ((x : A) (y : B x) → C (x , y))
         → ((t : Σᵉ A B) → C t)
ind-Σᵉ f (x , y) = f x y

--currying
curryᵉ : {i j k : Level}{A : UUᵉ i} {B : A → UUᵉ j} {C : Σᵉ A B → UUᵉ k}
         → ((t : Σᵉ A B) → C t)
         → ((x : A) (y : B x) → C (x , y))
curryᵉ f x y = f (x , y)

exo-dep-pairᵉ : {i j : Level} {A : UUᵉ i} {B : A → UUᵉ j} (w w' : Σᵉ A B)
              → UUᵉ (i ⊔ j)
exo-dep-pairᵉ w w' = Σᵉ ((pr1ᵉ w) =ₛᵉ (pr1ᵉ w')) (λ p → (exo-trᵉ _ p (pr2ᵉ w)) =ₛᵉ (pr2ᵉ w'))

dep-pair-=ₛᵉ :  {i j : Level} {A : UUᵉ i} {B : A → UUᵉ j} (w w' : Σᵉ A B)
             → (exo-dep-pairᵉ w w') → w =ₛᵉ w'
dep-pair-=ₛᵉ (a , b) (.a , .b) (reflₛᵉ , reflₛᵉ) = reflₛᵉ

inv-dep-pair-=ₛᵉ : {i j : Level} {A : UUᵉ i} {B : A → UUᵉ j} (w w' : Σᵉ A B)
                    → w =ₛᵉ w' → (exo-dep-pairᵉ w w')
inv-dep-pair-=ₛᵉ (a , b) (.a , .b) reflₛᵉ = reflₛᵉ , reflₛᵉ


--Path lifting property
exo-liftᵉ : {i j : Level} {A : UUᵉ i} {P : A → UUᵉ j} {x y : A}
            → (u : P x) (p : x =ₛᵉ y)
            → (x , u) =ₛᵉ (y , exo-trᵉ P p u)
exo-liftᵉ u reflₛᵉ = reflₛᵉ

--congruence
Σᵉ-form-cong1 : {i j : Level}{A : UUᵉ i}{P Q : A → UUᵉ j}
             → (P =ₛᵉ Q)
             → Σᵉ A P =ₛᵉ Σᵉ A Q
Σᵉ-form-cong1 reflₛᵉ = reflₛᵉ



-------------------------------------------------
--Type formers of products for exotypes
_×ᵉ_ :  {l1 l2 : Level}(A : UUᵉ l1) (B : UUᵉ l2) → UUᵉ (l1 ⊔ l2)
A ×ᵉ B = Σᵉ A (λ a → B)

×ᵉ-cong : {i j : Level}{A A' : UUᵉ i}{B B' : UUᵉ j}
          {p : A =ₛᵉ A'}{q : B =ₛᵉ B'}
          → A ×ᵉ B =ₛᵉ A' ×ᵉ B'
×ᵉ-cong {p = reflₛᵉ} {q = reflₛᵉ} = reflₛᵉ

exo-pairᵉ : {i j : Level} {A : UUᵉ i} {B : UUᵉ j} (x y : A ×ᵉ B)
              → UUᵉ (i ⊔ j)
exo-pairᵉ x y = ((pr1ᵉ x) =ₛᵉ (pr1ᵉ y)) ×ᵉ ((pr2ᵉ x) =ₛᵉ (pr2ᵉ y))

pair-=ₛᵉ : {i j : Level} {A : UUᵉ i} {B : UUᵉ j} (x y : A ×ᵉ B)
            → (exo-pairᵉ x y) → (x =ₛᵉ y) 
pair-=ₛᵉ (a , b) (.a , .b) (reflₛᵉ , reflₛᵉ) = reflₛᵉ

inv-pair-=ₛᵉ : {i j : Level} {A : UUᵉ i} {B : UUᵉ j} (x y : A ×ᵉ B)
                    → x =ₛᵉ y → (exo-pairᵉ x y)
inv-pair-=ₛᵉ x .x reflₛᵉ = reflₛᵉ , reflₛᵉ
