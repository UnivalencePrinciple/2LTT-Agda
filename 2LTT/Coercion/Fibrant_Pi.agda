{-# OPTIONS --without-K --exact-split --two-level --cumulativity #-}

module 2LTT.Coercion.Fibrant_Pi where

open import 2LTT.Exotypes public
open import 2LTT.Types public
open import 2LTT.Coercion.C public
open import 2LTT.Coercion.Fibrant_Conversion public


--Fibrancy is preserved under Πᵉ
isFibrant-Π : {i j : Level}{A : UUᵉ i}{B : A → UUᵉ j}
              → isFibrant {i} A → ((a : A) → isFibrant {j} (B a))
              → isFibrant {i ⊔ j} (Πᵉ A B)
isFibrant-Π {i} {j} {A = A} {B = B} (isfibrant fr P) Q = isfibrant T (fΠ ,ᵉ gΠ ,ᵉ gfΠ ,ᵉ fgΠ)
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
  T = Π fr (λ x → frB (g x))

  fΠ : Πᵉ A B → T
  fΠ X = λ x → fB (g x) (X (g x))

  gΠ : T → Πᵉ A B
  gΠ X = λ a → exo-tr B (gf a) (gB (g (f a)) (X (f a)))

  gfΠ : (X : Πᵉ A B) → gΠ (fΠ X) =ᵉ X
  gfΠ X = funextᵉ {i} {j} λ a → exo-concat (exo-ap (exo-tr B (gf a)) (gfB (g (f a)) (X (g (f a)))))
                                             (exo-apd {i} {j} X (gf a))

  fgΠ : (X : T) → fΠ (gΠ X) =ᵉ X
  fgΠ X = funextᵉ {i} {j} λ x → exo-concat (exo-ap-transport {i} {j} {A} {B} {frB} (gf (g x)) (fB) (gB (g (f (g x))) (X (f (g x)))))
                                             (exo-concat
                                              (exo-tr-elim {i} {j} {A} {frB} {p = (gf (g x))} (fgB (g (f (g x))) (X (f (g x)))))
                                              (exo-concat
                                               (exo-ap-tr {i} {j} {A} {frB} (UIPᵉ (gf (g x)) (exo-ap g (fg x))))
                                               (exo-concat
                                                (exo-inv (exo-tr-ap {i} {j} {fr} {A} {g} {frB} (fg x)))
                                                (exo-apd X (fg x)))))
