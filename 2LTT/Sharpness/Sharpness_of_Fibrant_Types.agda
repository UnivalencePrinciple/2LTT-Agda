{-# OPTIONS --without-K --exact-split --two-level --cumulativity #-}

module 2LTT.Sharpness.Sharpness_of_Fibrant_Types where

open import 2LTT.Sharpness.isSharp 


-------------------------------------------------------------------------
--If A and B are exo-equal exo-types, then A is sharp iff B is sharp.
=ᵉ-preserve-Sharp : {i k : Level} {A B : UUᵉ i}
                     → A =ᵉ B
                     → isSharp {i} A k
                     → isSharp {i} B k
=ᵉ-preserve-Sharp reflᵉ P = P


--------------------------------------------------------------------------
--Types are sharp
is-Type-Sharp : {i k : Level}{B : UU i}
                   → isSharp {i} B k
is-Type-Sharp {i} {k} {B} = issharp (is-Type-Cofibrant {i} {k} B )
                                    B
                                    id
                                    λ Y → id-is-equiv

--------------------------------------------------------------------------
--Fibrant exotypes are sharp
is-Fibrant-Sharp : {i j : Level}{B : UUᵉ i} → isFibrant {i} B → isSharp {i} B j
is-Fibrant-Sharp {i} {j} {B} P = issharp cwB
                                     fB
                                     ftB
                                     λ Y  → precomp-fibrant-equiv.proof
 where
 cwB = is-Fibrant-Cofibrant {i} {j} B P

 fB = isFibrant.fibrant-match P

 ftB = pr1ᵉ (isFibrant.fibrant-witness P)

 gtB = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness P))

 gftB = pr1ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness P)))

 fgtB = pr2ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness P)))
 
 module precomp-fibrant-equiv {Y : fB → UU j} where
  F = (precomp B fB ftB Y)
  
  G : Πᵉ B (Y ∘ᵉ ftB) → Π fB Y
  G X = λ a → exo-tr Y (fgtB a) (X (gtB a))

  GF : (X : Π fB Y) → G (F X) =ᵉ X
  GF X = funextᵉ (λ a → exo-apd {i} {j} X (fgtB a))

  FG : (X : Πᵉ B (Y ∘ᵉ ftB)) → F (G X) =ᵉ X
  FG X = funextᵉ (λ x → exo-concat (exo-ap-tr {i} {j} {fB} {Y} {ftB (gtB (ftB x))} {ftB x} {fgtB (ftB x)} {exo-ap ftB (gftB x)} (UIPᵉ _ _))
                    (exo-concat (exo-inv (exo-tr-ap (gftB x))) (exo-apd {i} {j} X (gftB x))))

  proof : Fib-isEquiv (isfibrant (Π fB Y) ≅-refl) (isCofibrant-at.Π-fibrant-witness (cwB (Y ∘ᵉ ftB))) F
  proof = Iso-to-Fib-isEquiv {i ⊔ j} {i ⊔ j} (isfibrant (Π fB Y) ≅-refl)
                                              (isCofibrant-at.Π-fibrant-witness (cwB (Y ∘ᵉ ftB)))
                                              F
                                              (G ,ᵉ GF ,ᵉ FG)

  

-------------------------------------------------------------------------
--In particular, ⊤̂ᵉ is sharp
is-⊤ᵉ-Sharp : {i : Level} (k : Level) → isSharp {i} (⊤ᵉ {i}) k
is-⊤ᵉ-Sharp {i} k = issharp ((⊤ᵉ-is-cofibrant {i}) k)
                      (⊤ {i}) 
                      (map-⊤ᵉ {i})
                      λ Y → id-is-equiv {i ⊔ k}
