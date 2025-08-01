{-# OPTIONS --without-K --exact-split  --two-level --cumulativity #-}

module 2LTT.Types.Functoriality where

open import 2LTT.Types.Functions
open import 2LTT.Types.Id_Type
open import 2LTT.Types.Pi
open import 2LTT.Primitive
open import 2LTT.Types.Sigma
open import 2LTT.Types.Type_Hierarchy
open import 2LTT.Types.Unit
open import 2LTT.Types.Retraction
open import 2LTT.Types.Coproduct
open import 2LTT.Types.Equivalences


--Π-functoriality
Π-functor : {i j : Level}{A B : UU i}{P : A → UU j}{Q : B → UU j}
             → (f0 : B → A ) → (f1 : (b : B) → P (f0 b) →  Q (b))
             → Π A P → Π B Q
Π-functor {i} {j} {A} {B} {P} {Q} f0 f1 = λ g → λ b → f1 b (g (f0 b))
{-# INLINE Π-functor #-}

Π-iso-cong : {i j : Level}{A B : UU i}{P : A → UU j}{Q : B → UU j}
             → (f0 : B → A) → {isEquiv {i} {i} f0}
             → (F : (b : B) → P (f0 b) → Q (b)) → {(b : B) → isEquiv {j} {j} (F b)}
             → _≃_ {i ⊔ j} {i ⊔ j} (Π A P) (Π B Q)
Π-iso-cong {i} {j} {A} {B} {P} {Q} f0 {W} F {U}
 = (Π-functor f0 F) , (invertibles-are-equiv {i ⊔ j} {i ⊔ j} (Π-functor f0 F)
                                                             ((Π-functor g0 G) , Htpy1 , Htpy2 ))
  where
  g0 : A → B
  g0 = pr1 (equivs-are-invertible _ W)

  gf0 : g0 ∘ f0 ~ id
  gf0 = pr1 (pr2 (equivs-are-invertible _ W))

  fg0 : f0 ∘ g0 ~ id
  fg0 = pr2 (pr2 (equivs-are-invertible _ W))

  fg0' : f0 ∘ g0 ~ id
  fg0' = pr1 (nat-htpy-of-invertible f0 (g0 , gf0 , fg0))

  naturality : (b : B) → Id (fg0' (f0 b)) (ap f0 (gf0 b))
  naturality b = (pr2 (nat-htpy-of-invertible f0 (g0 , gf0 , fg0)) b) ⁻¹

  F' : (b : B) → Q b → P (f0 b)
  F' b = pr1 (equivs-are-invertible _ (U b))

  F'F : (b : B) → (F' b) ∘ (F b) ~ id
  F'F b = pr1 (pr2 (equivs-are-invertible _ (U b)))

  FF' : (b : B) → (F b) ∘ (F' b) ~ id
  FF' b = pr2 (pr2 (equivs-are-invertible _ (U b)))

  G : (a : A) → Q (g0 a) → P a
  G a x = tr P (fg0' a) (F' (g0 a) x)

  Htpy1 : (Π-functor {i} {j} g0 G) ∘ (Π-functor {i} {j} f0 F) ~ id
  Htpy1 T = funext (λ a → tr-fam-ap {i} {j} {A} {P} {f0 (g0 a)} {a} {fg0' a}
                                     {f = (F' (g0 a)) ∘ (F (g0 a))} {g = id} {T (f0 (g0 a))} (funext (F'F (g0 a)))
                              · apd T (fg0' a))

  Htpy2 : (Π-functor {i} {j} f0 F) ∘ (Π-functor {i} {j} g0 G) ~ id
  Htpy2 T = funext {i ⊔ j} (λ b → ap {j} {j} (F b) (tr-cong {i} {j} {A} {P} {f0 (g0 (f0 b))} {f0 b} {fg0' (f0 b)} {ap {i} {i} f0 (gf0 b)}
                                                       {(F' (g0 (f0 b)) (T (g0 (f0 b))))} (naturality b))  ·
                   (ap {j} {j} (F b) ((tr-ap {i} {j} {B} {A} {f0} {P} (gf0 b)) ⁻¹) ·
                   (ap {j} {j} (F b) (apd (λ b → (F' b) (T b)) (gf0 b)) · (FF' b) (T b))))

Π-iso-cong' : {i j : Level}{A B : UU i}{P : A → UU j}{Q : B → UU j}
             → (W : B ≃ A) 
             → (f1 : (b : B) → P ((pr1 W) b) ≃ Q (b))
             → Π A P ≃ Π B Q
Π-iso-cong' W V
             = Π-iso-cong (pr1 W) {pr2 W} (λ (b : _) → pr1 (V b)) {λ (b : _) → pr2 (V b)}

