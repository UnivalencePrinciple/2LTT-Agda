{-# OPTIONS --without-K --exact-split --two-level --cumulativity #-}

module 2LTT.Coercion.Fibrant_Sigma where

open import 2LTT.Exotypes public
open import 2LTT.Types public
open import 2LTT.Coercion.C public
open import 2LTT.Coercion.Fibrant_Conversion public

--Fibrancy is preserved under Σᵉ
isFibrant-Σ : {i j : Level}{A : UUᵉ i}{B : A → UUᵉ j}
              → isFibrant {i} A → ((a : A) → isFibrant {j} (B a))
              → isFibrant {i ⊔ j} (Σᵉ A B)
isFibrant-Σ {i} {j} {A = A} {B = B} (isfibrant fr P) Q = isfibrant (Σ fr (frB ∘ᵉ g)) (≅-trans iso-1 iso-2)
  where
  f : A → fr
  f = pr1ᵉ P

  g : fr → A
  g = pr1ᵉ (pr2ᵉ P)

  gf : (a : A) → (g (f a)) =ᵉ a
  gf = (pr1ᵉ (pr2ᵉ (pr2ᵉ P)))

  frB : (a : A) → UU j
  frB a = isFibrant.fibrant-match (Q a)

  iso-1 : (Σᵉ A B) ≅ Σᵉ fr (λ x → frB (g x))
  iso-1 = Σᵉ-iso-cong' {i} {j} P
                            (exo-tr (λ u → ((a : A) → _≅_ {j} {j} (B a) (frB (u a))))
                                    (exo-inv (funextᵉ gf))
                                    (λ a → (isFibrant.fibrant-witness (Q a))) )

  iso-2 : Σᵉ fr (λ x → frB (g x)) ≅ Σ fr (frB ∘ᵉ g)
  iso-2 = exo-Σᵉ-equiv
  
------------------------------------------------------------------------------------------------------------------------
--Fibrancy is preserved under ×ᵉ
isFibrant-× : {i j : Level}{A : UUᵉ i}{B : UUᵉ j}
              → isFibrant {i} A → isFibrant {j} B
              → isFibrant {i ⊔ j} (A ×ᵉ B)
isFibrant-× {i} {j} {A = A} {B = B} (isfibrant RA wA) (isfibrant RB wB)
  = isfibrant (RA × RB) (fA×B ,ᵉ gA×B ,ᵉ gfA×B ,ᵉ fgA×B)
  where
  fA : A → RA
  fA = pr1ᵉ wA

  gA : RA → A
  gA = pr1ᵉ (pr2ᵉ wA)

  gfA : (a : A) → (gA (fA a)) =ᵉ a
  gfA = (pr1ᵉ (pr2ᵉ (pr2ᵉ wA)))

  fgA : (x : RA) → (fA (gA x)) =ᵉ x
  fgA = (pr2ᵉ (pr2ᵉ (pr2ᵉ wA)))

  fB : B → RB
  fB = pr1ᵉ wB

  gB : RB → B
  gB = pr1ᵉ (pr2ᵉ wB)

  gfB : (a : B) → (gB (fB a)) =ᵉ a
  gfB = (pr1ᵉ (pr2ᵉ (pr2ᵉ wB)))

  fgB : (x : RB) → (fB (gB x)) =ᵉ x
  fgB = (pr2ᵉ (pr2ᵉ (pr2ᵉ wB)))

  fA×B : A ×ᵉ B → RA × RB
  fA×B (a ,ᵉ b) = fA a , fB b

  gA×B : RA × RB → A ×ᵉ B
  gA×B (x , y) = gA x ,ᵉ gB y

  gfA×B : (w : _) → gA×B (fA×B w) =ᵉ w
  gfA×B (a ,ᵉ b) = pair-=ᵉ _ _ (gfA a ,ᵉ gfB b)

  fgA×B : (w : _) → fA×B (gA×B w) =ᵉ w
  fgA×B (x , y) = pair-=ᵉ' _ _ (fgA x ,ᵉ fgB y)
