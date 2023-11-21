{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT_C.Cofibration.Cofibrancy_of_Coproduct where

open import 2LTT_C.Cofibration.isCofibrant public


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

  fA : Πᵉ A (λ x → C (Y (inlᵉ x))) → C frA
  fA = pr1ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P (λ x → Y (inlᵉ x)))))

  gA : C frA → Πᵉ A (λ x → C (Y (inlᵉ x)))
  gA = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P (λ x → Y (inlᵉ x))))))

  gfA : (T : Πᵉ A (λ x → C (Y (inlᵉ x)))) → gA (fA T) =ᵉ T
  gfA = pr1ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P (λ x → Y (inlᵉ x)))))))

  fgA : (T : C frA) → fA (gA T) =ᵉ T
  fgA = pr2ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P (λ x → Y (inlᵉ x)))))))

  witA : isFibrant (Πᵉ A (λ t → C (Y (inlᵉ t))))
  witA = isfibrant frA (fA ,ᵉ gA ,ᵉ gfA ,ᵉ fgA)

  ctrA : ((a : A) → is-contr (Y (inlᵉ a))) → (Fib-is-contr {i ⊔ k} (Πᵉ A (λ t → C (Y (inlᵉ t))))
                                                                   {isCofibrant-at.Π-fibrant-witness (P (λ x → Y (inlᵉ x)))})
  ctrA = isCofibrant-at.contr-preserve-witness (P (λ x → Y (inlᵉ x)))

  frB : UU (j ⊔ k)
  frB = isFibrant.fibrant-match (isCofibrant-at.Π-fibrant-witness (Q (λ x → Y (inrᵉ x))))

  fB : Πᵉ B (λ x → C (Y (inrᵉ x))) → C frB
  fB = pr1ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (Q (λ x → Y (inrᵉ x)))))

  gB : C frB → Πᵉ B (λ x → C (Y (inrᵉ x)))
  gB = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (Q (λ x → Y (inrᵉ x))))))

  gfB : (T : Πᵉ B (λ x → C (Y (inrᵉ x)))) → gB (fB T) =ᵉ T
  gfB = pr1ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (Q (λ x → Y (inrᵉ x)))))))

  fgB : (T : C frB) → fB (gB T) =ᵉ T
  fgB = pr2ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (Q (λ x → Y (inrᵉ x)))))))

  witB : isFibrant (Πᵉ B (λ t → C (Y (inrᵉ t))))
  witB = isfibrant frB (fB ,ᵉ gB ,ᵉ gfB ,ᵉ fgB)

  ctrB : ((x : B) → is-contr (Y (inrᵉ x))) → (Fib-is-contr {j ⊔ k} (Πᵉ B (λ t → C (Y (inrᵉ t))))
                                                                   {isCofibrant-at.Π-fibrant-witness (Q (λ x → Y (inrᵉ x)))})
  ctrB = isCofibrant-at.contr-preserve-witness (Q (λ x → Y (inrᵉ x)))

  frA+B : UU (i ⊔ j ⊔ k)
  frA+B = frA × frB

  fA+B : Πᵉ (A +ᵉ B) (λ x → C (Y x)) → C frA+B
  fA+B w = c (ic (fA (λ x → w (inlᵉ x))) , ic (fB (λ x → w (inrᵉ x)))) 

  gA+B : C frA+B → Πᵉ (A +ᵉ B) (λ x → C (Y x))
  gA+B (c (x , y)) (inlᵉ a) = gA (c x) a 
  gA+B (c (x , y)) (inrᵉ b) = gB (c y) b

  gfA+B : (T : Πᵉ (A +ᵉ B) (λ x → C (Y x))) → gA+B (fA+B T) =ᵉ T
  gfA+B T = funextᵉ {i ⊔ j} {k} λ {(inlᵉ x) → happlyᵉ (gfA (T ∘ᵉ inlᵉ)) x   ;
                                    (inrᵉ x) → happlyᵉ (gfB (T ∘ᵉ inrᵉ)) x }

  fgA+B : (T : C frA+B) → fA+B (gA+B T) =ᵉ T
  fgA+B (c (x , y)) = pair-=ᵉ' _ _ (fgA (c x) ,ᵉ fgB (c y)) 
