{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT.Exotypes.Sigma where

open import 2LTT.Primitive
open import 2LTT.Exotypes.Exo_Equality


--Type formers of dependent pairs for exotypes
record Σᵉ {i j} (A : UUᵉ i) (B : A → UUᵉ j) : UUᵉ (i ⊔ j) where
  constructor _,ᵉ_
  field
    pr1ᵉ : A
    pr2ᵉ : B pr1ᵉ

open Σᵉ public

infixr 4 _,ᵉ_

--η-law for Σᵉ type
η-law-Σᵉ : {i j : Level}{A : UUᵉ i} {B : A → UUᵉ j} → (x : Σᵉ A B) → (x =ᵉ (pr1ᵉ x ,ᵉ pr2ᵉ x))
η-law-Σᵉ x = reflᵉ

--induction principle for Σᵉ
ind-Σᵉ : {i j k : Level}{A : UUᵉ i} {B : A → UUᵉ j} {C : Σᵉ A B → UUᵉ k}
         → ((x : A) (y : B x) → C (x ,ᵉ y))
         → ((t : Σᵉ A B) → C t)
ind-Σᵉ f (x ,ᵉ y) = f x y

--currying
curryᵉ : {i j k : Level}{A : UUᵉ i} {B : A → UUᵉ j} {C : Σᵉ A B → UUᵉ k}
         → ((t : Σᵉ A B) → C t)
         → ((x : A) (y : B x) → C (x ,ᵉ y))
curryᵉ f x y = f (x ,ᵉ y)

exo-dep-pairᵉ : {i j : Level} {A : UUᵉ i} {B : A → UUᵉ j} (w w' : Σᵉ A B)
              → UUᵉ (i ⊔ j)
exo-dep-pairᵉ w w' = Σᵉ ((pr1ᵉ w) =ᵉ (pr1ᵉ w')) (λ p → (exo-tr _ p (pr2ᵉ w)) =ᵉ (pr2ᵉ w'))

dep-pair-=ᵉ :  {i j : Level} {A : UUᵉ i} {B : A → UUᵉ j} (w w' : Σᵉ A B)
             → (exo-dep-pairᵉ w w') → w =ᵉ w'
dep-pair-=ᵉ (a ,ᵉ b) (.a ,ᵉ .b) (reflᵉ ,ᵉ reflᵉ) = reflᵉ

inv-dep-pair-=ᵉ : {i j : Level} {A : UUᵉ i} {B : A → UUᵉ j} (w w' : Σᵉ A B)
                    → w =ᵉ w' → (exo-dep-pairᵉ w w')
inv-dep-pair-=ᵉ (a ,ᵉ b) (.a ,ᵉ .b) reflᵉ = reflᵉ ,ᵉ reflᵉ


--Path lifting property
exo-liftᵉ : {i j : Level} {A : UUᵉ i} {P : A → UUᵉ j} {y : A} (u : Σᵉ {i} {j} A P) (p : (pr1ᵉ u) =ᵉ y)
            → u =ᵉ (y ,ᵉ exo-tr P p (pr2ᵉ u))
exo-liftᵉ u reflᵉ = reflᵉ

--congruence
Σᵉ-form-cong1 : {i j : Level}{A : UUᵉ i}{P Q : A → UUᵉ j}
             → (P =ᵉ Q)
             → Σᵉ A P =ᵉ Σᵉ A Q
Σᵉ-form-cong1 reflᵉ = reflᵉ



-------------------------------------------------
--Type formers of products for exotypes
_×ᵉ_ :  {l1 l2 : Level}(A : UUᵉ l1) (B : UUᵉ l2) → UUᵉ (l1 ⊔ l2)
A ×ᵉ B = Σᵉ A (λ a → B)

×ᵉ-cong : {i j : Level}{A A' : UUᵉ i}{B B' : UUᵉ j}
          {p : A =ᵉ A'}{q : B =ᵉ B'}
          → A ×ᵉ B =ᵉ A' ×ᵉ B'
×ᵉ-cong {p = reflᵉ} {q = reflᵉ} = reflᵉ

exo-pairᵉ : {i j : Level} {A : UUᵉ i} {B : UUᵉ j} (x y : A ×ᵉ B)
              → UUᵉ (i ⊔ j)
exo-pairᵉ x y = ((pr1ᵉ x) =ᵉ (pr1ᵉ y)) ×ᵉ ((pr2ᵉ x) =ᵉ (pr2ᵉ y))

pair-=ᵉ : {i j : Level} {A : UUᵉ i} {B : UUᵉ j} (x y : A ×ᵉ B)
            → (exo-pairᵉ x y) → (x =ᵉ y) 
pair-=ᵉ (a ,ᵉ b) (.a ,ᵉ .b) (reflᵉ ,ᵉ reflᵉ) = reflᵉ

inv-pair-=ᵉ : {i j : Level} {A : UUᵉ i} {B : UUᵉ j} (x y : A ×ᵉ B)
                    → x =ᵉ y → (exo-pairᵉ x y)
inv-pair-=ᵉ x .x reflᵉ = reflᵉ ,ᵉ reflᵉ


×ᵉ-of-maps : {i j i' j' : Level} {A : UUᵉ i} {A' : UUᵉ i'} {B : UUᵉ j} {B' : UUᵉ j'}
            → (f : A → B) (f' : A' → B')
            → (A ×ᵉ A' → B ×ᵉ B')
×ᵉ-of-maps f f' (a ,ᵉ a') = (f a ,ᵉ f' a')
