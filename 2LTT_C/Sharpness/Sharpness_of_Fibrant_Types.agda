{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT_C.Sharpness.Sharpness_of_Fibrant_Types where

open import 2LTT_C.Sharpness.isSharp 


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
                   → isSharp {i} (C B) k
is-Type-Sharp {i} {k} {B} = issharp (is-Type-Cofibrant {i} {k} B )
                                    B
                                    (λ {(c x) → x})
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

 ftB = λ x → ic (pr1ᵉ (isFibrant.fibrant-witness P) x)

 gtB = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness P))

 gftB = pr1ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness P)))

 fgtB = pr2ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness P)))
 
 module precomp-fibrant-equiv {Y : fB → UU j} where
  F = (precomp B fB ftB Y)

  F' = F ∘ᵉ map-Πᵉ 

  G : Πᵉ B (λ x → C (Y (ftB x))) → Πᵉ (C fB) (λ x → C (Y (ic x)))
  G T = λ a → exo-tr (λ x → C (Y (ic x))) (fgtB a) (T (gtB a))

  GF' : (T : Πᵉ (C fB) (λ x → C (Y (ic x)))) → G (F' T) =ᵉ T
  GF' T = funextᵉ (λ a → exo-apd {i} {j} T (fgtB a))

  F'G : (T : Πᵉ B (λ x → C (Y (ftB x)))) → F' (G T) =ᵉ T
  F'G T = funextᵉ (λ x → exo-concat
                          (exo-ap-tr {P = λ b → C (Y (ic b))} {e₁ = fgtB (c (ftB x))} {e₂ = exo-ap (λ x → c (ftB x)) (gftB x)} (UIPᵉ _ _))
                          (exo-concat (exo-inv (exo-tr-ap (gftB x))) (exo-apd T (gftB x))))

  proof : Fib-isEquiv (isfibrant (Π fB Y) ≅-refl) (isCofibrant-at.Π-fibrant-witness (cwB (λ x → Y (ftB x)))) F
  proof = Fib-First-2-out-of-3-rule
             (isfibrant _ exo-Πᵉ-equiv) (isfibrant _ ≅-refl) (isCofibrant-at.Π-fibrant-witness (cwB (λ x → Y (ftB x))))
             map-Πᵉ F
             (Iso-to-Fib-isEquiv (isfibrant _ exo-Πᵉ-equiv) (isfibrant _ ≅-refl) map-Πᵉ is-map-Πᵉ-iso )
             (Iso-to-Fib-isEquiv (isfibrant _ exo-Πᵉ-equiv)
                  ((isCofibrant-at.Π-fibrant-witness (cwB (λ x → Y (ftB x))))) (F ∘ᵉ map-Πᵉ) (G ,ᵉ (GF' ,ᵉ F'G)))

-------------------------------------------------------------------------
--In particular, ⊤̂ᵉ is sharp
is-⊤ᵉ-Sharp : {i : Level} (k : Level) → isSharp {i} (⊤ᵉ {i}) k
is-⊤ᵉ-Sharp {i} k = issharp ((⊤ᵉ-is-cofibrant {i}) k)
                      (⊤ {i}) 
                      (λ x → ic (map-⊤ᵉ x))
                      λ Y → id-is-equiv {i ⊔ k}
