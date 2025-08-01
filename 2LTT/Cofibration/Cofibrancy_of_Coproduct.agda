{-# OPTIONS --without-K --exact-split --two-level --cumulativity #-}

module 2LTT.Cofibration.Cofibrancy_of_Coproduct where

open import 2LTT.Coercion.Fibrant_Conversion public
open import 2LTT.Coercion.Fibrant_Type_Hierarchy public
open import 2LTT.Cofibration.isCofibrant public



+ᵉ-preserve-Cofibrant : {i j k : Level}{A : UUᵉ i}{B : UUᵉ j}
                               → isCofibrant {i} A k → isCofibrant {j} B k
                               → isCofibrant {i ⊔ j} (A +ᵉ B) k
+ᵉ-preserve-Cofibrant {i} {j} {k} {A} {B} P Q Y
    = iscofibrant-at
        (isfibrant (frA × frB)
                   (fA+B ,ᵉ gA+B ,ᵉ gfA+B ,ᵉ fgA+B))
        λ K → ×-contr-is-contr (ctrA (λ x → K (inlᵉ x))) (ctrB (λ x → K (inrᵉ x)))
  where
  frA : UU (i ⊔ k)
  frA = isFibrant.fibrant-match (isCofibrant-at.Π-fibrant-witness (P (λ x → Y (inlᵉ x))))

  fA : Πᵉ A (λ x → Y (inlᵉ x)) → frA
  fA = pr1ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P (λ x → Y (inlᵉ x)))))

  gA : frA → Πᵉ A (λ x → Y (inlᵉ x))
  gA = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P (λ x → Y (inlᵉ x))))))

  gfA : (T : Πᵉ A (λ x → Y (inlᵉ x))) → gA (fA T) =ᵉ T
  gfA = pr1ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P (λ x → Y (inlᵉ x)))))))

  fgA : (T : frA) → fA (gA T) =ᵉ T
  fgA = pr2ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P (λ x → Y (inlᵉ x)))))))

  witA : isFibrant (Πᵉ A (Y ∘ᵉ inlᵉ))
  witA = isfibrant frA (fA ,ᵉ gA ,ᵉ gfA ,ᵉ fgA)

  ctrA :  Πᵉ A (λ x → is-contr (Y (inlᵉ x))) → (Fib-is-contr {i ⊔ k} (Πᵉ A (Y ∘ᵉ inlᵉ))
                                                                   {isCofibrant-at.Π-fibrant-witness (P (λ x → Y (inlᵉ x)))})
  ctrA = isCofibrant-at.contr-preserve-witness (P (λ x → Y (inlᵉ x)))

  frB : UU (j ⊔ k)
  frB = isFibrant.fibrant-match (isCofibrant-at.Π-fibrant-witness (Q (λ x → Y (inrᵉ x))))

  fB : Πᵉ B (λ x → Y (inrᵉ x)) → frB
  fB = pr1ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (Q (λ x → Y (inrᵉ x)))))

  gB : frB → Πᵉ B (λ x → Y (inrᵉ x))
  gB = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (Q (λ x → Y (inrᵉ x))))))

  gfB : (T : Πᵉ B (λ x → Y (inrᵉ x))) → gB (fB T) =ᵉ T
  gfB = pr1ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (Q (λ x → Y (inrᵉ x)))))))

  fgB : (T : frB) → fB (gB T) =ᵉ T
  fgB = pr2ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (Q (λ x → Y (inrᵉ x)))))))

  witB : isFibrant (Πᵉ B (Y ∘ᵉ inrᵉ))
  witB = isfibrant frB (fB ,ᵉ gB ,ᵉ gfB ,ᵉ fgB)

  ctrB : Πᵉ B (λ x → is-contr (Y (inrᵉ x))) → (Fib-is-contr {j ⊔ k} (Πᵉ B (Y ∘ᵉ inrᵉ))
                                                                   {isCofibrant-at.Π-fibrant-witness (Q (λ x → Y (inrᵉ x)))})
  ctrB = isCofibrant-at.contr-preserve-witness (Q (λ x → Y (inrᵉ x)))

  frA+B : UU (i ⊔ j ⊔ k)
  frA+B = frA × frB

  fA+B : Πᵉ (A +ᵉ B) Y → frA+B
  fA+B w = fA (w ∘ᵉ inlᵉ) , fB (w ∘ᵉ inrᵉ)

  gA+B : frA+B → Πᵉ (A +ᵉ B) Y
  gA+B (x , y) (inlᵉ a) = gA x a 
  gA+B (x , y) (inrᵉ b) = gB y b

  gfA+B : (T : Πᵉ (A +ᵉ B) Y) → gA+B (fA+B T) =ᵉ T
  gfA+B T = funextᵉ {i ⊔ j} {k} λ {(inlᵉ x) → happlyᵉ (gfA (T ∘ᵉ inlᵉ)) x   ;
                                    (inrᵉ x) → happlyᵉ (gfB (T ∘ᵉ inrᵉ)) x }

  fgA+B : (T : frA+B) → fA+B (gA+B T) =ᵉ T
  fgA+B (x , y) = pair-=ᵉ' _ _ (fgA x ,ᵉ fgB y) 
