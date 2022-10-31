{-# OPTIONS --without-K --exact-split --two-level --cumulativity #-}

module 2LTT.Cofibration.Cofibrancy_of_Fibrant_Types where

open import 2LTT.Coercion.Fibrant_Conversion public
open import 2LTT.Coercion.Fibrant_Type_Hierarchy public
open import 2LTT.Cofibration.isCofibrant public
open import 2LTT.Coercion.Fibrant_Unit public


--All types is cofibrant
is-Type-Cofibrant : {i j : Level}(B : UU i) →  isCofibrant {i} B j
is-Type-Cofibrant {i} {j} B Y = iscofibrant-at (isfibrant (Π B Y) ≅-refl)                                                                  
                                                λ K → Π-type-contr λ a → K a

--All fibrant exo-types is cofibrant
is-Fibrant-Cofibrant : {i j : Level}(A : UUᵉ i) → isFibrant {i} A → isCofibrant {i} A j
isFibrant.fibrant-match (isCofibrant-at.Π-fibrant-witness (is-Fibrant-Cofibrant {i} {j} A (isfibrant fr (f ,ᵉ g ,ᵉ gf ,ᵉ fg)) Y))
    = Π fr (λ x → Y (g x))
isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (is-Fibrant-Cofibrant {i} {j} A (isfibrant fr (f ,ᵉ g ,ᵉ gf ,ᵉ fg)) Y))
    = (λ T x → T (g x)) ,ᵉ
      (λ T a → exo-tr {i} {j} Y (gf a) (T (f a))) ,ᵉ
      (λ T → funextᵉ {i} {j} (λ a → exo-apd T (gf a))) ,ᵉ
      (λ T → funextᵉ {i} {j} (λ x →  exo-concat
                                           (exo-ap-tr (UIPᵉ (gf (g x))
                                             (exo-ap {i} {i} g (fg x))))
                                           ((exo-concat
                                               (exo-inv (exo-tr-ap (fg x)))
                                               (exo-apd {i} {j} T (fg x))))))
isCofibrant-at.contr-preserve-witness (is-Fibrant-Cofibrant {i} {j} A (isfibrant fr (f ,ᵉ g ,ᵉ gf ,ᵉ fg)) Y)
    = Fib-Π-type-contr {i} {j} {A} {isfibrant fr (f ,ᵉ g ,ᵉ gf ,ᵉ fg)}
                               {Y} {λ a → isfibrant (Y a) ≅-refl}


--In particular, ⊤ᵉ is cofibrant
⊤ᵉ-is-cofibrant : {i : Level} (k : Level) → isCofibrant {i} (⊤ᵉ {i}) k
isFibrant.fibrant-match (isCofibrant-at.Π-fibrant-witness (⊤ᵉ-is-cofibrant {i} k Y))
  = Π ⊤ λ {star → Y starᵉ}
isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (⊤ᵉ-is-cofibrant {i} k Y))
  = (λ T → λ {star → T (starᵉ) }) ,ᵉ
    (λ T → λ {starᵉ → T (star)}) ,ᵉ
    (λ a → reflᵉ) ,ᵉ
    (λ b → reflᵉ)
isCofibrant-at.contr-preserve-witness (⊤ᵉ-is-cofibrant {i} k Y)
 = Fib-Π-type-contr {i} {k} {⊤ᵉ {i}} {isFibrant-⊤ᵉ {i}} {Y} {λ a → isfibrant (Y a) ≅-refl}
