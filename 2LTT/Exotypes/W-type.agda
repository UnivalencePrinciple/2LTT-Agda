{-# OPTIONS --without-K --two-level --cumulativity #-}

module 2LTT.Exotypes.W-type where

open import 2LTT.Primitive
open import 2LTT.Exotypes.Naturals
open import 2LTT.Exotypes.Exo_Equality
open import 2LTT.Exotypes.Finite
open import 2LTT.Exotypes.Coproduct
open import 2LTT.Exotypes.Empty
open import 2LTT.Exotypes.Functions
open import 2LTT.Exotypes.Unit
open import 2LTT.Exotypes.Sigma


data WWᵉ {l1 l2 : Level}(A : UUᵉ l1) (B : A → UUᵉ l2) : UUᵉ (l1 ⊔ l2)  where
  supᵉ : (a : A) → ((B a → WWᵉ A B) → WWᵉ A B)

WWᵉ-ind : {l1 l2 l3 : Level}(A : UUᵉ l1) (B : A → UUᵉ l2) (Y : WWᵉ {l1} {l2} A B → UUᵉ l3) →
                            ((a : A) (f : B (a) → WWᵉ {l1} {l2} A B)
                            (h : ((b : B (a)) → Y (f (b)))) → Y (supᵉ a f)) →
                            ((s : WWᵉ A B) → Y s)
WWᵉ-ind {l1} {l2} {l3} A B Y X (supᵉ a g) = X a g (λ b → WWᵉ-ind {l1} {l2} {l3} A B Y X (g b))


--Another version of ℕᵉ in terms of Wᵉ-types
new-ℕᵉ = WWᵉ (ℕᵉ< twoᵉ) (λ {(inlᵉ (inrᵉ starᵉ)) → ⊥ᵉ ; (inrᵉ starᵉ) → ⊤ᵉ})

ℕᵉ-to-new-ℕᵉ : ℕᵉ → new-ℕᵉ
ℕᵉ-to-new-ℕᵉ zeroᵉ = supᵉ (inlᵉ (inrᵉ starᵉ)) ex-falsoᵉ
ℕᵉ-to-new-ℕᵉ (succᵉ n) = supᵉ (inrᵉ starᵉ) (λ {starᵉ → ℕᵉ-to-new-ℕᵉ n})

new-ℕᵉ-to-ℕᵉ : new-ℕᵉ → ℕᵉ
new-ℕᵉ-to-ℕᵉ (supᵉ (inlᵉ (inrᵉ starᵉ)) f) = zeroᵉ
new-ℕᵉ-to-ℕᵉ (supᵉ (inrᵉ starᵉ) f) = succᵉ (new-ℕᵉ-to-ℕᵉ (f starᵉ))

ℕᵉ-to-new-ℕᵉ-is-sec : (x : new-ℕᵉ) → ℕᵉ-to-new-ℕᵉ (new-ℕᵉ-to-ℕᵉ x) =ᵉ x
ℕᵉ-to-new-ℕᵉ-is-sec (supᵉ (inlᵉ (inrᵉ starᵉ)) f) = exo-ap (supᵉ (inlᵉ (inrᵉ starᵉ))) (funextᵉ λ {()})
ℕᵉ-to-new-ℕᵉ-is-sec (supᵉ (inrᵉ starᵉ) f) = exo-ap (supᵉ (inrᵉ starᵉ)) (funextᵉ (λ {starᵉ → ℕᵉ-to-new-ℕᵉ-is-sec (f starᵉ)}))

ℕᵉ-to-new-ℕᵉ-is-retr : (x : ℕᵉ) → new-ℕᵉ-to-ℕᵉ (ℕᵉ-to-new-ℕᵉ x) =ᵉ x
ℕᵉ-to-new-ℕᵉ-is-retr zeroᵉ = reflᵉ
ℕᵉ-to-new-ℕᵉ-is-retr (succᵉ x) = exo-ap succᵉ (ℕᵉ-to-new-ℕᵉ-is-retr x)

ℕᵉ≅new-ℕᵉ : ℕᵉ ≅ new-ℕᵉ
ℕᵉ≅new-ℕᵉ = ℕᵉ-to-new-ℕᵉ ,ᵉ (new-ℕᵉ-to-ℕᵉ ,ᵉ (ℕᵉ-to-new-ℕᵉ-is-retr ,ᵉ ℕᵉ-to-new-ℕᵉ-is-sec ))
