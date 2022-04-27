{-# OPTIONS --without-K --two-level --cumulativity #-}

module 2LTT.Coercion.Fibrant_Sigma where

open import 2LTT.Exotypes public
open import 2LTT.Types public
open import 2LTT.Coercion.C public
open import 2LTT.Coercion.Fibrant_Conversion public

--Fibrancy is preserved under Σᵉ
isFibrant-Σ : {i j : Level}{A : UUᵉ i}{B : A → UUᵉ j}
              → isFibrant {i} A → ((a : A) → isFibrant {j} (B a))
              → isFibrant {i ⊔ j} (Σᵉ A B)
isFibrant-Σ {i} {j} {A = A} {B = B} (isfibrant fr P) Q = isfibrant T ((fΣ , gΣ , gfΣ , fgΣ))
  where
  f : A → fr
  f = pr1ᵉ P

  g : fr → A
  g = pr1ᵉ (pr2ᵉ P)

  gf : (a : A) → (g (f a)) =ᵉ a
  gf = (pr1ᵉ (pr2ᵉ (pr2ᵉ P)))

  fg : (x : fr) → (f (g x)) =ᵉ x
  fg = (pr2ᵉ (pr2ᵉ (pr2ᵉ P)))

  frB : (a : A) → UU j
  frB a = isFibrant.fibrant-match (Q a)

  fB : (a : A) → (B a) → (frB a)
  fB a = pr1ᵉ (isFibrant.fibrant-witness (Q a))

  gB : (a : A) → (frB a) → (B a)
  gB a = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness (Q a)))

  gfB : (a : A) → (b : B a) → (gB a (fB a b)) =ᵉ b
  gfB a = (pr1ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness (Q a)))))

  fgB : (a : A) → (y : frB a) → (fB a (gB a y)) =ᵉ y
  fgB a = (pr2ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness (Q a)))))

  T : UU (i ⊔ j)
  T = Σ fr (λ x → frB (g x))

  fΣ : (Σᵉ A B) → T
  fΣ (a , b) = f a , fB (g (f a)) (exo-tr B (exo-inv (gf a)) b)

  gΣ : T → (Σᵉ A B)
  gΣ (x , y) = g x , gB (g x) y

  gfΣ : (u : Σᵉ A B) → gΣ (fΣ u) =ᵉ u
  gfΣ (a , b) = dep-pair-=ᵉ _ _ (gf a , exo-concat
                                         (exo-tr-elim {x = g (f a)} {y = a} {p = gf a} (gfB (g (f a)) (exo-tr B (exo-inv (gf a)) b)))
                                         (exo-concat (exo-tr-concat (exo-inv (gf a)) (gf a)) (exo-tr-left-law B (gf a))))

  fgΣ : (v : T) → fΣ (gΣ v) =ᵉ v
  fgΣ (x , y) = (dep-pair-=ᵉ' _ _  ((fg x) , exo-concat
                                              (exo-ap (exo-tr (frB ∘ᵉ g) (fg x))
                                                        (exo-ap-transport {i} {j} {A} {B} {frB} {g x} {g (f (g x))}
                                                         (exo-inv (gf (g x))) (fB) (gB (g x) y)))
                                              (exo-concat (exo-tr-ap {i} {j} {fr} {A} {g} {frB} (fg x))
                                                           (exo-concat
                                                            (exo-tr-concat {i} {j} {A} {frB} (exo-inv (gf (g x))) (exo-ap {i}{i} g (fg x)))
                                                            (exo-concat
                                                              (exo-ap-tr {i} {j} {A} {frB}
                                                                     (UIPᵉ (exo-concat (exo-inv (gf (g x))) (exo-ap g (fg x))) reflᵉ))
                                                              (fgB (g x) y))))))

------------------------------------------------------------------------------------------------------------------------
--Fibrancy is preserved under ×ᵉ
isFibrant-× : {i j : Level}{A : UUᵉ i}{B : UUᵉ j}
              → isFibrant {i} A → isFibrant {j} B
              → isFibrant {i ⊔ j} (A ×ᵉ B)
isFibrant-× {i} {j} {A = A} {B = B} (isfibrant RA wA) (isfibrant RB wB)
  = isfibrant (RA × RB) (fA×B , gA×B , gfA×B , fgA×B)
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
  fA×B (a , b) = fA a , fB b

  gA×B : RA × RB → A ×ᵉ B
  gA×B (x , y) = gA x , gB y

  gfA×B : (w : _) → gA×B (fA×B w) =ᵉ w
  gfA×B (a , b) = pair-=ᵉ _ _ (gfA a , gfB b)

  fgA×B : (w : _) → fA×B (gA×B w) =ᵉ w
  fgA×B (x , y) = pair-=ᵉ' _ _ (fgA x , fgB y)



  
