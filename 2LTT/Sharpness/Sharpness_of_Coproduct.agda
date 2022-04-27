{-# OPTIONS --without-K --two-level --cumulativity #-}

module 2LTT.Sharpness.Sharpness_of_Coproduct where

open import 2LTT.Cofibration public
open import 2LTT.Sharpness.isSharp public

-----------------------------------------------------------------------------------------
--If A and B are sharp, then A + B is sharp
+ᵉ-preserve-Sharp : {i j k : Level}{A : UUᵉ i}{B : UUᵉ j}
                               → isSharp {i} A k → isSharp {j} B k
                               → isSharp {i ⊔ j} (A +ᵉ B) k
+ᵉ-preserve-Sharp {i} {j} {k} {A} {B} P Q
 = issharp (cfwA+B)
           (RA + RB)
           ηA+B
           λ Y → precomp-+-equiv.proof
  where
  cfwA : isCofibrant A k
  cfwA = isSharp.cofibrant-witness P

  RA : UU i
  RA = isSharp.fibrant-replacement P

  ηA : A → RA
  ηA = isSharp.fibrant-transfer P
  
  cfwB : isCofibrant B k
  cfwB = isSharp.cofibrant-witness Q
  
  RB : UU j
  RB = isSharp.fibrant-replacement Q

  ηB : B → RB
  ηB = isSharp.fibrant-transfer Q

  cfwA+B : isCofibrant (A +ᵉ B) k
  cfwA+B = +ᵉ-preserve-Cofibrant cfwA cfwB

  ηA+B : A +ᵉ B → RA + RB
  ηA+B (inlᵉ x) = inl (ηA x)
  ηA+B (inrᵉ x) = inr (ηB x)

  --A Commutative Square
  module precomp-+-equiv {Y : _+_ {i} {j} RA RB → UU k} where
    fibrant1 : isFibrant (Πᵉ (A +ᵉ B) (Y ∘ᵉ ηA+B))
    fibrant1 = isCofibrant-at.Π-fibrant-witness (cfwA+B (Y ∘ᵉ ηA+B))

    fibrant2 : isFibrant (Πᵉ A (Y ∘ᵉ (inl ∘ᵉ ηA)) ×ᵉ Πᵉ B (Y ∘ᵉ (inr ∘ᵉ ηB)))
    fibrant2 = (isFibrant-× {i ⊔ k} {j ⊔ k} (isCofibrant-at.Π-fibrant-witness (cfwA (Y ∘ᵉ (inl ∘ᵉ ηA))))
                                            (isCofibrant-at.Π-fibrant-witness (cfwB (Y ∘ᵉ (inr ∘ᵉ ηB)))))

    fibrant3 : isFibrant (Πᵉ A (Y ∘ᵉ (inl ∘ᵉ ηA)))
    fibrant3 = isCofibrant-at.Π-fibrant-witness (cfwA (Y ∘ᵉ (inl ∘ᵉ ηA)))

    fibrant4 : isFibrant (Πᵉ B (Y ∘ᵉ (inr ∘ᵉ ηB)))
    fibrant4 = isCofibrant-at.Π-fibrant-witness (cfwB (Y ∘ᵉ (inr ∘ᵉ ηB)))

    Fib-EqA : Fib-isEquiv (isfibrant _ ≅-refl) fibrant3 (precomp A RA ηA _)
    Fib-EqA = (isSharp.precomp-is-equiv P) (Y ∘ᵉ (inl))

    Fib-EqB : Fib-isEquiv (isfibrant _ ≅-refl) fibrant4 (precomp B RB ηB _)
    Fib-EqB = (isSharp.precomp-is-equiv Q) (Y ∘ᵉ (inr))
    
    v-left : Π (RA + RB) Y → Πᵉ (A +ᵉ B) (Y ∘ᵉ ηA+B)
    v-left = precomp (A +ᵉ B) (RA + RB) ηA+B Y

    h-top : Π (RA + RB) Y → Π RA (Y ∘ inl) × Π RB (Y ∘ inr)
    h-top = Π-+-expansion

    v-right : Π RA (Y ∘ inl) × Π RB (Y ∘ inr) → Πᵉ A (Y ∘ᵉ (inl ∘ᵉ ηA)) ×ᵉ Πᵉ B (Y ∘ᵉ (inr ∘ᵉ ηB))
    v-right (S , T) = (precomp A RA ηA _) S , (precomp B RB ηB _) T

    h-bot : Πᵉ (A +ᵉ B) (Y ∘ᵉ ηA+B) →  Πᵉ A (Y ∘ᵉ (inl ∘ᵉ ηA)) ×ᵉ Πᵉ B (Y ∘ᵉ (inr ∘ᵉ ηB))
    h-bot = pr1ᵉ (Πᵉ-+-expansion)

    CS : (T : Π (RA + RB) Y) → h-bot (v-left T) =ᵉ v-right (h-top T)
    CS T = reflᵉ

    proof : Fib-isEquiv (isfibrant _ ≅-refl) (isCofibrant-at.Π-fibrant-witness (cfwA+B (Y ∘ᵉ ηA+B))) v-left
    proof = Fib-First-3-out-of-4-rule  {i ⊔ j ⊔ k} {i ⊔ j ⊔ k} {i ⊔ j ⊔ k} {i ⊔ j ⊔ k}
                                       (isfibrant _ ≅-refl) (isfibrant _ ≅-refl)
                                       (fibrant1) (fibrant2)
                                       h-top v-left v-right h-bot CS
                                       Π-+-expansion-is-equiv
                                       (Fib-×-isEquiv {i ⊔ k} {i ⊔ k} {j ⊔ k} {j ⊔ k}
                                                      (isfibrant _ ≅-refl) fibrant3
                                                      (isfibrant _ ≅-refl) fibrant4
                                                      (precomp A RA ηA _) (precomp B RB ηB _)
                                                      Fib-EqA  Fib-EqB)
                                       (Iso-to-Fib-isEquiv {i ⊔ j ⊔ k} {i ⊔ j ⊔ k}
                                                           {Πᵉ (A +ᵉ B) (Y ∘ᵉ ηA+B)}
                                                           {Πᵉ A (Y ∘ᵉ (inl ∘ᵉ ηA)) ×ᵉ Πᵉ B (Y ∘ᵉ (inr ∘ᵉ ηB))}
                                                           fibrant1 fibrant2 h-bot (pr2ᵉ (Πᵉ-+-expansion {i} {j} {k})))

    
