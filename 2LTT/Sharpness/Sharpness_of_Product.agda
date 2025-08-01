{-# OPTIONS --without-K --exact-split --two-level --cumulativity #-}

module 2LTT.Sharpness.Sharpness_of_Product where

open import 2LTT.Sharpness.isSharp public


×ᵉ-preserve-Sharp : {i j k : Level}{A : UUᵉ i}{B : UUᵉ j}
                               → isSharp {i} A (j ⊔ k) → isSharp {j} B k
                               → isSharp {i ⊔ j} (A ×ᵉ B) k
×ᵉ-preserve-Sharp {i} {j} {k} {A} {B} (issharp cwA RA rA pequivA)
                                      (issharp cwB RB rB pequivB)
                                      = issharp cwA×B (_×_ {i} {j} RA RB) rA×B (λ Y → precomp-equiv.proof {Y})
  where
    rA×B : A ×ᵉ B → RA × RB
    rA×B (a ,ᵉ b) = (rA a , rB b)

    cwA×B = ×ᵉ-preserve-Cofibrant cwA cwB

    module precomp-equiv {Y : (_×_ {i} {j} RA RB) → UU k} where
        ΠType-1 : UU (i ⊔ j ⊔ k) --this is fibrant by default.
        ΠType-1 = Π (RA × RB) Y

        ΠType-2 : UU (i ⊔ j ⊔ k) --this is fibrant by default.
        ΠType-2 = Π RA (λ c → Π RB (λ d → Y (c , d)))

        ΠType-3 : UUᵉ (i ⊔ j ⊔ k) 
        ΠType-3 = Πᵉ A (λ a → Π RB (λ d → Y (rA a , d)))

        ΠType-4 : UUᵉ (i ⊔ j ⊔ k) 
        ΠType-4 = Πᵉ A (λ a → Πᵉ B (λ b → Y (rA a , rB b)))

        ΠType-5 : UUᵉ (i ⊔ j ⊔ k) 
        ΠType-5 = Πᵉ (A ×ᵉ B) (Y ∘ᵉ rA×B)

        Fibrant3 = (isCofibrant-at.Π-fibrant-witness (cwA λ a → Π RB (λ d → Y (rA a , d))))

        Fibrant4 = (isFibrant-iso (≅-sym {i ⊔ j ⊔ k}{i ⊔ j ⊔ k} Πᵉ-×-expansion) (isCofibrant-at.Π-fibrant-witness (cwA×B (Y ∘ᵉ rA×B))))

        Fibrant5 = (isCofibrant-at.Π-fibrant-witness (cwA×B (Y ∘ᵉ rA×B)))
        
        Map1 : ΠType-1 → ΠType-2
        Map1 = λ x x₁ x₂ → x (x₁ , x₂)

        Map2 : ΠType-2 → ΠType-3
        Map2 = λ x x₁ x₂ → x (rA x₁) x₂

        Map3 : ΠType-3 → ΠType-4
        Map3 = λ x x₁ x₂ → x x₁ (rB x₂)

        Map4 : ΠType-4 → ΠType-5
        Map4 = λ x x₁ → x (pr1ᵉ x₁) (pr2ᵉ x₁)

        Map-main : ΠType-1 → ΠType-5
        Map-main = λ x x₁ → x (rA×B x₁)

        Main-Htp : (T : _) → Map4 (Map3 (Map2 (Map1 T))) =ᵉ Map-main T
        Main-Htp T = reflᵉ

        Equiv-main : Fib-isEquiv (isfibrant ΠType-1 ≅-refl) Fibrant5 (Map4 ∘ᵉ (Map3 ∘ᵉ (Map2 ∘ᵉ Map1)))
        Equiv-main = Fib-comp-isEquiv {i ⊔ j ⊔ k}{i ⊔ j ⊔ k} {i ⊔ j ⊔ k}
                                      (isfibrant ΠType-1 ≅-refl)
                                      Fibrant4
                                      Fibrant5
                                      (Map3 ∘ᵉ (Map2 ∘ᵉ Map1))
                                      Map4
                                      (Fib-comp-isEquiv {i ⊔ j ⊔ k}{i ⊔ j ⊔ k} {i ⊔ j ⊔ k}
                                      (isfibrant ΠType-1 ≅-refl)
                                      Fibrant3
                                      Fibrant4
                                      (Map2 ∘ᵉ Map1)
                                      Map3
                                      (Fib-comp-isEquiv {i ⊔ j ⊔ k}{i ⊔ j ⊔ k} {i ⊔ j ⊔ k}
                                      (isfibrant ΠType-1 ≅-refl)
                                      (isfibrant ΠType-2 ≅-refl)
                                      Fibrant3
                                      Map1
                                      Map2
                                      Π-×-expansion-is-equiv
                                      (pequivA (λ c →  Π RB (λ d → Y (c , d)))))
                                      (Fib-Π-functor-isEquiv cwA (λ a → pequivB (λ d → Y (rA a , d)))))
                                      (Iso-to-Fib-isEquiv Fibrant4 Fibrant5 (pr1ᵉ Πᵉ-×-expansion) (pr2ᵉ Πᵉ-×-expansion))
        -------------------------
        proof : Fib-isEquiv (isfibrant _ ≅-refl) Fibrant5 Map-main
        proof = Fib-htpy-to-isEquiv (isfibrant _ ≅-refl)
                                    Fibrant5
                                    (Map4 ∘ᵉ (Map3 ∘ᵉ (Map2 ∘ᵉ Map1)))
                                    Map-main
                                    Main-Htp
                                    Equiv-main
        

        
        
