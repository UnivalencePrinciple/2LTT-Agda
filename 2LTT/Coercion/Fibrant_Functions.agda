{-# OPTIONS --without-K --two-level --cumulativity #-}

module 2LTT.Coercion.Fibrant_Functions where

open import 2LTT.Exotypes public
open import 2LTT.Types public
open import 2LTT.Coercion.C public
open import 2LTT.Coercion.Fibrant_Conversion public

--Fibrancy is preserved under exo-isomorphisms
isFibrant-iso : {i : Level}{A B : UUᵉ i}
              → A ≅ B → isFibrant {i} A
              → isFibrant {i} B
isFibrant-iso {i} {A} {B} I (isfibrant fr fw) = isfibrant fr (f' , g' , gf' , fg')
  where
  f : A → fr
  f = pr1ᵉ fw

  g : fr → A
  g = pr1ᵉ (pr2ᵉ fw)

  gf : (a : A) → (g (f a)) =ᵉ a
  gf = (pr1ᵉ (pr2ᵉ (pr2ᵉ fw)))

  fg : (x : fr) → (f (g x)) =ᵉ x
  fg = (pr2ᵉ (pr2ᵉ (pr2ᵉ fw)))

  F : A → B
  F = pr1ᵉ I

  G : B → A
  G = pr1ᵉ (pr2ᵉ I)

  GF : (a : A) → G (F a) =ᵉ a
  GF = (pr1ᵉ (pr2ᵉ (pr2ᵉ I)))

  FG : (b : B) → F (G b) =ᵉ b
  FG = (pr2ᵉ (pr2ᵉ (pr2ᵉ I)))

  f' : B → fr
  f' = f ∘ᵉ G

  g' : fr → B
  g' = F ∘ᵉ g

  gf' : (b : B) → (g' (f' b)) =ᵉ b
  gf' b = exo-concat (exo-ap F (gf (G b))) (FG b)

  fg' : (x : fr) → (f' (g' x)) =ᵉ x
  fg' x = exo-concat (exo-ap f (GF (g x))) (fg x)
