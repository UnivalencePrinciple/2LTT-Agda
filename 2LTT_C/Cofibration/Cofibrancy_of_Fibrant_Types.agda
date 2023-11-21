{-# OPTIONS --without-K --exact-split --two-level  #-}

module 2LTT_C.Cofibration.Cofibrancy_of_Fibrant_Types where


open import 2LTT_C.Cofibration.isCofibrant public
open import 2LTT_C.Coercion.Fibrant_Unit public


--All types is cofibrant
is-Type-Cofibrant : {i j : Level}(B : UU i) → isCofibrant {i} (C B) j
is-Type-Cofibrant {i} {j} B Y =
  iscofibrant-at (isfibrant (Π B (λ b → Y (c b))) exo-Πᵉ-equiv)
    λ K → Π-type-contr (λ a → K (c a))

--All fibrant exo-types is cofibrant
is-Fibrant-Cofibrant : {i j : Level}(A : UUᵉ i) → isFibrant {i} A → isCofibrant {i} A j
isFibrant.fibrant-match (isCofibrant-at.Π-fibrant-witness (is-Fibrant-Cofibrant {i} {j} A (isfibrant fr (f ,ᵉ g ,ᵉ gf ,ᵉ fg)) Y))
    = Π fr (λ x → Y (g (c x)))
isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (is-Fibrant-Cofibrant {i} {j} A (isfibrant fr (f ,ᵉ g ,ᵉ gf ,ᵉ fg)) Y))
    = ≅-trans ((λ T → λ x → T (g x)) ,ᵉ
               (λ T a → exo-tr {i} {j} (λ x → C (Y x)) (gf a) (T (f a)) ) ,ᵉ
              ((λ T → funextᵉ {i} {j} (λ a → exo-apd T (gf a))) ,ᵉ
               (λ T → funextᵉ {i} {j} (λ x →  exo-concat
                                           (exo-ap-tr (UIPᵉ (gf (g x))
                                             (exo-ap {i} {i} g (fg x))))
                                           ((exo-concat
                                               (exo-inv (exo-tr-ap (fg x)))
                                               (exo-apd {i} {j} T (fg x))))))))
              (exo-Πᵉ-equiv)
      
isCofibrant-at.contr-preserve-witness (is-Fibrant-Cofibrant {i} {j} A (isfibrant fr (f ,ᵉ g ,ᵉ gf ,ᵉ fg)) Y)
    = Fib-Π-type-contr {i} {j} {A} {isfibrant fr (f ,ᵉ g ,ᵉ gf ,ᵉ fg)}
                               {λ x → C (Y x)} {λ a → isfibrant (Y a) ≅-refl}


--In particular, ⊤ᵉ is cofibrant
⊤ᵉ-is-cofibrant : {i : Level} (k : Level) → isCofibrant {i} (⊤ᵉ {i}) k
isFibrant.fibrant-match (isCofibrant-at.Π-fibrant-witness (⊤ᵉ-is-cofibrant {i} k Y))
  = Π ⊤ λ {star → Y starᵉ}
isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (⊤ᵉ-is-cofibrant {i} k Y))
  = (λ T → c (λ {star → ic (T starᵉ)})) ,ᵉ
    (λ T → λ {starᵉ → c ((ic T) star)}) ,ᵉ
    (λ a → reflᵉ) ,ᵉ
    (λ b → reflᵉ)
isCofibrant-at.contr-preserve-witness (⊤ᵉ-is-cofibrant {i} k Y)
 = Fib-Π-type-contr {i} {k} {⊤ᵉ {i}} {isFibrant-⊤ᵉ {i}} {λ x → C (Y x)} {λ a → isfibrant (Y a) ≅-refl}
