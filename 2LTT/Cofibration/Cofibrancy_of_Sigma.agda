{-# OPTIONS --without-K --two-level --cumulativity #-}

module 2LTT.Cofibration.Cofibrancy_of_Sigma where

open import 2LTT.Coercion.Fibrant_Conversion public
open import 2LTT.Coercion.Fibrant_Type_Hierarchy public
open import 2LTT.Cofibration.isCofibrant public

Σᵉ-preserve-Cofibrant : {i j k : Level}{A : UUᵉ i}{B : A → UUᵉ j}
                        → isCofibrant {i} A (j ⊔ k) → ((a : A) → isCofibrant {j} (B a) k)
                        → isCofibrant {i ⊔ j} (Σᵉ A B) k
Σᵉ-preserve-Cofibrant {i} {j} {k} {A} {B} P Q Y
  = iscofibrant-at
      (isfibrant frΣAB
                 (fΣAB , gΣAB , gfΣAB , fgΣAB))
      (λ K → contrA (λ a → (contrB a) λ b → K (a , b)))
  where
  frB : (a : A) → UU (j ⊔ k)
  frB a = isFibrant.fibrant-match (isCofibrant-at.Π-fibrant-witness ((Q a) (λ b → Y (a , b))))

  fB : (a : A) → (Πᵉ (B a) (λ b → Y (a , b))) → (frB a)
  fB a = pr1ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness ((Q a) (λ b → Y (a , b)))))

  gB : (a : A) → (frB a) → (Πᵉ (B a) (λ b → Y (a , b)))
  gB a = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness ((Q a) (λ b → Y (a , b))))))

  gfB : (a : A) → (T : (Πᵉ (B a) (λ b → Y (a , b)))) → (gB a (fB a T)) =ᵉ T
  gfB a = pr1ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness ((Q a) (λ b → Y (a , b)))))))

  fgB : (a : A) → (T : frB a) → (fB a (gB a T)) =ᵉ T
  fgB a = pr2ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness ((Q a) (λ b → Y (a , b)))))))

  contrB : (a : A) →  Πᵉ (B a) (λ b → is-contr (Y (a , b))) → (Fib-is-contr (Πᵉ (B a) (λ b → Y (a , b)))
                                                                         {isfibrant (frB a) (fB a , gB a , gfB a , fgB a)})
  contrB a = isCofibrant-at.contr-preserve-witness ((Q a) (λ b → Y (a , b)))

  frΣAB : UU (i ⊔ j ⊔ k)
  frΣAB = isFibrant.fibrant-match (isCofibrant-at.Π-fibrant-witness (P (λ a → frB a)))

  fA : Πᵉ A frB → frΣAB
  fA = pr1ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P (λ a → frB a))))

  gA : frΣAB → Πᵉ A frB
  gA = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P (λ a → frB a)))))

  gfA : (T : Πᵉ A frB) → gA (fA T) =ᵉ T
  gfA = pr1ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P (λ a → frB a))))))

  fgA : (T : frΣAB) → fA (gA T) =ᵉ T
  fgA = pr2ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P (λ a → frB a))))))

  contrA :  Πᵉ A (λ a → is-contr (frB a)) → (Fib-is-contr (Πᵉ A frB) {isfibrant (frΣAB) (fA , gA , gfA , fgA)})
  contrA = isCofibrant-at.contr-preserve-witness (P (λ a → frB a))

  fΣAB : Πᵉ (Σᵉ A B) Y → frΣAB
  fΣAB T = fA (λ a → (fB a) (λ b → T (a , b)))

  gΣAB : frΣAB → Πᵉ (Σᵉ A B) Y
  gΣAB T (a , b) = (gB a) ((gA T) a) b

  gfΣAB : (T : Πᵉ (Σᵉ A B) Y) → gΣAB (fΣAB T) =ᵉ T
  gfΣAB T = funextᵉ {i ⊔ j} {k} (λ {(a , b) → exo-concat (exo-ap (λ (X : Πᵉ A frB) → (gB a) (X a) b)
                                                                    (gfA (λ a' → (fB a') (λ b' → T (a' , b')))))
                                                           (Πᵉ-elim-cong reflᵉ ((gfB a) (λ b' → T (a , b'))))})

  fgΣAB : (T : frΣAB) → fΣAB (gΣAB T) =ᵉ T
  fgΣAB T = exo-concat ((exo-ap fA (funextᵉ {i} {j ⊔ k}  (λ a → (fgB a) ((gA T) a))))) (fgA T)


---------------------------------------------------------------------------------------------------------
×ᵉ-preserve-Cofibrant : {i j k : Level}{A : UUᵉ i}{B : UUᵉ j}
                               → isCofibrant {i} A (j ⊔ k)→ isCofibrant {j} B k
                               → isCofibrant {i ⊔ j} (A ×ᵉ B) k
×ᵉ-preserve-Cofibrant {i} {j} {k} {A} {B} P Q = Σᵉ-preserve-Cofibrant {i} {j} {k} {A} {λ _ → B} P (λ _ → Q)

 
