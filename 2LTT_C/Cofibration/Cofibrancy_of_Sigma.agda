{-# OPTIONS --without-K --exact-split --two-level  #-}

module 2LTT_C.Cofibration.Cofibrancy_of_Sigma where


open import 2LTT_C.Cofibration.isCofibrant public

Σᵉ-preserve-Cofibrant : {i j k : Level}{A : UUᵉ i}{B : A → UUᵉ j}
                        → isCofibrant {i} A (j ⊔ k) → ((a : A) → isCofibrant {j} (B a) k)
                        → isCofibrant {i ⊔ j} (Σᵉ A B) k
Σᵉ-preserve-Cofibrant {i} {j} {k} {A} {B} P Q Y
  = iscofibrant-at
      (isfibrant frΣAB
                 (fΣAB ,ᵉ gΣAB ,ᵉ gfΣAB ,ᵉ fgΣAB))
      (λ K → contrA (λ a → (contrB a) λ b → K (a ,ᵉ b)))
  where
  frB : (a : A) → UU (j ⊔ k)
  frB a = isFibrant.fibrant-match (isCofibrant-at.Π-fibrant-witness ((Q a) (λ b → Y (a ,ᵉ b))))

  fB : (a : A) → (Πᵉ (B a) (λ b → C (Y (a ,ᵉ b)))) → C (frB a)
  fB a = pr1ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness ((Q a) (λ b → Y (a ,ᵉ b)))))

  gB : (a : A) → C (frB a) → (Πᵉ (B a) (λ b → C (Y (a ,ᵉ b))))
  gB a = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness ((Q a) (λ b → Y (a ,ᵉ b))))))

  gfB : (a : A) → (T : (Πᵉ (B a) (λ b → C (Y (a ,ᵉ b))))) → (gB a (fB a T)) =ᵉ T
  gfB a = pr1ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness ((Q a) (λ b → Y (a ,ᵉ b)))))))

  fgB : (a : A) → (T : C (frB a)) → (fB a (gB a T)) =ᵉ T
  fgB a = pr2ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness ((Q a) (λ b → Y (a ,ᵉ b)))))))

  contrB : (a : A) →  ((b : B a) → is-contr (Y (a ,ᵉ b))) → (Fib-is-contr (Πᵉ (B a) (λ b → C (Y (a ,ᵉ b))))
                                                                         {isfibrant (frB a) (fB a ,ᵉ gB a ,ᵉ gfB a ,ᵉ fgB a)})
  contrB a = isCofibrant-at.contr-preserve-witness ((Q a) (λ b → Y (a ,ᵉ b)))

  frΣAB : UU (i ⊔ j ⊔ k)
  frΣAB = isFibrant.fibrant-match (isCofibrant-at.Π-fibrant-witness (P (λ a → frB a)))

  fA : Πᵉ A (λ a → C (frB a)) → C frΣAB
  fA = pr1ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P (λ a → frB a))))

  gA : C frΣAB → Πᵉ A  (λ a → C (frB a))
  gA = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P (λ a → frB a)))))

  gfA : (T : Πᵉ A (λ a → C (frB a))) → gA (fA T) =ᵉ T
  gfA = pr1ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P (λ a → frB a))))))

  fgA : (T : C frΣAB) → fA (gA T) =ᵉ T
  fgA = pr2ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P (λ a → frB a))))))

  contrA :  ((a : A) → is-contr (frB a)) → (Fib-is-contr (Πᵉ A (λ a → C (frB a))) {isfibrant (frΣAB) (fA ,ᵉ gA ,ᵉ gfA ,ᵉ fgA)})
  contrA = isCofibrant-at.contr-preserve-witness (P (λ a → frB a))

  fΣAB : Πᵉ (Σᵉ A B) (λ x → C (Y x)) → C frΣAB
  fΣAB T = fA (λ a → (fB a) (λ b → T (a ,ᵉ b)))

  gΣAB : C frΣAB → Πᵉ (Σᵉ A B) (λ x → C (Y x))
  gΣAB T (a ,ᵉ b) = (gB a) ((gA T) a) b

  gfΣAB : (T : Πᵉ (Σᵉ A B) (λ x → C (Y x))) → gΣAB (fΣAB T) =ᵉ T
  gfΣAB T = funextᵉ {i ⊔ j} {k} (λ {(a ,ᵉ b) → exo-concat (exo-ap (λ (X : Πᵉ A (λ a → C (frB a))) → (gB a) (X a) b)
                                                                    (gfA (λ a' → (fB a') (λ b' → T (a' ,ᵉ b')))))
                                                           (Πᵉ-elim-cong reflᵉ ((gfB a) (λ b' → T (a ,ᵉ b'))))})

  fgΣAB : (T : C frΣAB) → fΣAB (gΣAB T) =ᵉ T
  fgΣAB T = exo-concat ((exo-ap fA (funextᵉ {i} {j ⊔ k}  (λ a → (fgB a) ((gA T) a))))) (fgA T)


---------------------------------------------------------------------------------------------------------
×ᵉ-preserve-Cofibrant : {i j k : Level}{A : UUᵉ i}{B : UUᵉ j}
                               → isCofibrant {i} A (j ⊔ k)→ isCofibrant {j} B k
                               → isCofibrant {i ⊔ j} (A ×ᵉ B) k
×ᵉ-preserve-Cofibrant {i} {j} {k} {A} {B} P Q = Σᵉ-preserve-Cofibrant {i} {j} {k} {A} {λ _ → B} P (λ _ → Q)

 
