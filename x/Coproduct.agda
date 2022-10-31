{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT.Exotypes.Coproduct where

open import 2LTT.Primitive 
open import 2LTT.Exotypes.Exo_Equality 
open import 2LTT.Exotypes.Pi
open import 2LTT.Exotypes.Sigma
open import 2LTT.Exotypes.Functions


--Type formers of coproducts for exotypes 
data _+ᵉ_ {l1 l2 : Level}(A : UUᵉ l1) (B : UUᵉ l2) : UUᵉ (l1 ⊔ l2)  where
  inlᵉ : A → A +ᵉ B
  inrᵉ : B → A +ᵉ B

--induction principle for coprod
ind-+ᵉ : {i j k : Level} {A : UUᵉ i} {B : UUᵉ j} (C : A +ᵉ B → UUᵉ k)
              → ((x : A) → C (inlᵉ x)) → ((y : B) → C (inrᵉ y))
              → (t : A +ᵉ B) → C t
ind-+ᵉ C f g (inlᵉ x) = f x
ind-+ᵉ C f g (inrᵉ x) = g x

inrᵉ-fmly : {i j k : Level} {A : UUᵉ i} {B : UUᵉ j} (C : A +ᵉ B → UUᵉ k)
           → (B → UUᵉ k)
inrᵉ-fmly C = λ b → C (inrᵉ b)

inlᵉ-fmly : {i j k : Level} {A : UUᵉ i} {B : UUᵉ j} (C : A +ᵉ B → UUᵉ k)
           → (A → UUᵉ k)
inlᵉ-fmly C = λ a → C (inlᵉ a)

Πᵉ-+-expansion : {i j k : Level} {A : UUᵉ i} {B : UUᵉ j} {C : A +ᵉ B → UUᵉ k}
                →  Πᵉ (A +ᵉ B) C ≅ (Πᵉ A (λ a → C (inlᵉ a)) ×ᵉ Πᵉ B (λ b → C (inrᵉ b)))
Πᵉ-+-expansion = (λ F → (λ a → F (inlᵉ a)) ,ᵉ λ b → F (inrᵉ b)) ,ᵉ
                 (λ (f ,ᵉ g) → λ { (inlᵉ x) → f x ; (inrᵉ x) → g x}) ,ᵉ
                 (λ x → funextᵉ λ { (inlᵉ x) → reflᵉ ; (inrᵉ x) → reflᵉ}) ,ᵉ
                 (λ x → reflᵉ)

