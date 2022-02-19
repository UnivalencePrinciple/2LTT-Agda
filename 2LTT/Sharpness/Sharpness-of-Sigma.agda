{-# OPTIONS --without-K --two-level --cumulativity #-}

module 2LTT.Sharpness.Sharpness-of-Sigma where

open import 2LTT.Sharpness.isSharp public

--------------------
--INCOMPLETE!!!
--------------------

Σᵉ-preserve-Sharp : {i j : Level}{A : UUᵉ i}{B : A → UUᵉ j}
                               → isSharp {i} A → ((a : A) → isSharp {j} (B a))
                               → isSharp {i ⊔ j} (Σᵉ A B)
Σᵉ-preserve-Sharp {i} {j} {A} {B} P Q = issharp (cwΣAB)
                                                (Σ frA (λ x → RB̃ x))
                                                (ftΣ)
                                                λ k Y → {!!} 
  where
   cwA : isCofibrant A
   cwA = isSharp.cofibrant-witness P
-------
   frA : UU i
   frA = isSharp.fibrant-replacement P
-------
   ftA : A → frA
   ftA = isSharp.fibrant-transfer P
-------
   midset : UU (i ⊔ lsuc j)
   midset = isFibrant.fibrant-match
              (isCofibrant-at.Π-fibrant-witness (cwA (lsuc j) (λ _ → UU j)))
-------            
   F : (frA → UU j) → midset
   F = (precomp A (cwA) (frA) (ftA) (λ _ → UU j))
-------
   pcmpeqA : (k : Level) (Y : frA → UU k)
                 → isEquiv (precomp {i} {k} A cwA frA ftA Y)
   pcmpeqA = isSharp.precomp-is-equiv P
-------
   G : midset → (frA → UU j)
   G = pr1 (equivs-are-invertible F (pcmpeqA (lsuc j) (λ _ → UU j)))
-------
   GF : (G ∘ F) ~ id
   GF = pr1 (pr2 (equivs-are-invertible F (pcmpeqA (lsuc j) (λ _ → UU j))))
-------
   FG : (F ∘ G) ~ id
   FG = pr2 (pr2 (equivs-are-invertible F (pcmpeqA (lsuc j) (λ _ → UU j))))
-------   
   CWB : (a : A) → isCofibrant (B a)
   CWB a = isSharp.cofibrant-witness (Q a)
-------
   cwΣAB : isCofibrant (Σᵉ A B)
   cwΣAB = Σᵉ-preserve-Cofibrant cwA CWB
-------
   RB : (a : A) → UU j
   RB a = isSharp.fibrant-replacement (Q a)
-------
   FTB : (a : A) → ((B a) → (RB a))
   FTB a = isSharp.fibrant-transfer (Q a)
-------
   α : (A → UU j) → midset
   α = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness
                   (isCofibrant-at.Π-fibrant-witness (cwA (lsuc j) (λ _ → UU j)))))
-------
   β : midset → (A → UU j)
   β = pr1ᵉ (isFibrant.fibrant-witness
                   (isCofibrant-at.Π-fibrant-witness (cwA (lsuc j) (λ _ → UU j))))
-------
   αβ : (α ∘ᵉ β) =ₛᵉ idᵉ
   αβ = pr1ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness
                   (isCofibrant-at.Π-fibrant-witness (cwA (lsuc j) (λ _ → UU j))))))
-------
   βα : (β ∘ᵉ α) =ₛᵉ idᵉ
   βα = pr2ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness
                   (isCofibrant-at.Π-fibrant-witness (cwA (lsuc j) (λ _ → UU j))))))
-------
   RB̃ : frA → UU j
   RB̃ = G (α RB)
-------
   ev : A → ((A → UU j) → UU j)
   ev a Y = Y a
-------
   eṽ : A → (midset → UU j)
   eṽ a = (ev a) ∘ᵉ β
-------
   L1 : Id (α (λ a → RB̃ (ftA a))) (α RB)
   L1 = (ap F {RB̃} {G (α RB)} refl) · FG (α RB)
-------
   L2 : (a : A) → (Id {lsuc j} {UU j} (RB̃ (ftA a)) (RB a))
   L2 a = (=ₛᵉ-to-Id (exo-apᵉ {i ⊔ lsuc j} {lsuc j} (ev a) (happlyₛᵉ βα (λ a' → RB̃ (ftA a'))))) ⁻¹ ·
               ((ap {i ⊔ lsuc j} {lsuc j} {midset} {UU j} (eṽ a) {α (λ a → RB̃ (ftA a))} {α RB} (L1)) ·
                   =ₛᵉ-to-Id (exo-apᵉ {i ⊔ lsuc j} {lsuc j} (ev a) (happlyₛᵉ βα RB)))
-------
   EQ-T : (a : A) → (RB a) → ((λ a → RB̃ (ftA a)) a)
   EQ-T a = (inv p q)
       where
        p : ((λ a → RB̃ (ftA a)) a) → (RB a)
        p = pr1 ((idtoeqv (L2 a)))

        q : isEquiv p
        q = pr2 (idtoeqv (L2 a))
-------
   EQ-T' : (a : A) → ((λ a → RB̃ (ftA a)) a) → (RB a)
   EQ-T' a = pr1 ((idtoeqv (L2 a)))
-------
   ftΣ : (Σᵉ A B) → (Σ {i} {j} frA (λ x → RB̃ x))
   ftΣ = (λ x → ftA (pr1ᵉ x) , (EQ-T (pr1ᵉ x)) ((FTB (pr1ᵉ x)) (pr2ᵉ x)))
-------
   module precomp-equiv {k : Level} {Y : Σ {i} {j} frA (λ x → RB̃ x) → UU k} where
        last-type-1 : UU (i ⊔ j ⊔ k)
        last-type-1 = isFibrant.fibrant-match (isCofibrant-at.Π-fibrant-witness
                                      (cwΣAB k (λ e → Y (ftA (pr1ᵉ e) , EQ-T (pr1ᵉ e) (FTB (pr1ᵉ e) (pr2ᵉ e))))))
      ---------
        m1 : last-type-1 → (Πᵉ (Σᵉ A B) (λ e → Y (ftA (pr1ᵉ e) , EQ-T (pr1ᵉ e) (FTB (pr1ᵉ e) (pr2ᵉ e)))))
        m1 = pr1ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness
                                      (cwΣAB k (λ e → Y (ftA (pr1ᵉ e) , EQ-T (pr1ᵉ e) (FTB (pr1ᵉ e) (pr2ᵉ e)))))))
      ---------
        n1 : (Πᵉ (Σᵉ A B) (λ e → Y (ftA (pr1ᵉ e) , EQ-T (pr1ᵉ e) (FTB (pr1ᵉ e) (pr2ᵉ e))))) → last-type-1
        n1 = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness
                                      (cwΣAB k (λ e → Y (ftA (pr1ᵉ e) , EQ-T (pr1ᵉ e) (FTB (pr1ᵉ e) (pr2ᵉ e))))))))
      ---------
        nm1 : (n1 ∘ᵉ m1) =ₛᵉ idᵉ
        nm1 = pr1ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness
                                      (cwΣAB k (λ e → Y (ftA (pr1ᵉ e) , EQ-T (pr1ᵉ e) (FTB (pr1ᵉ e) (pr2ᵉ e)))))))))
      ---------
        mn1 : (m1 ∘ᵉ n1) =ₛᵉ idᵉ
        mn1 = pr2ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness
                                      (cwΣAB k (λ e → Y (ftA (pr1ᵉ e) , EQ-T (pr1ᵉ e) (FTB (pr1ᵉ e) (pr2ᵉ e)))))))))
      ---------
        f1 : (Π (Σ {i} {j} frA (λ x → RB̃ x)) Y) → last-type-1
        f1 =  precomp (Σᵉ A B) (cwΣAB) (Σ frA (λ x → (RB̃ x))) (λ {(a , b) → ((ftA a) , (EQ-T a) ((FTB a) b))}) Y
      ---------
        f2 : (Π (Σ {i} {j} frA (λ x → RB̃ x)) Y)
             → (Π frA (λ x → Π (RB̃ x) (λ y → Y (x , y))))
        f2 = Π-Σ-expansion
      ---------
        f3 : (Π frA (λ x → Π (RB̃ x) (λ y → Y (x , y)))) → last-type-1
        f3 = λ x → n1 λ {(a , b) → x (ftA a) (EQ-T a (FTB a b))}
      ---------
        dd : (f3 ∘ f2) ~ (f1)
        dd = λ x → refl
      ---------
        ww : isEquiv f3
        ww = invertibles-are-equiv f3
                                  ((λ x ra rb → {!!}) ,
                                   {!!} ,
                                   {!!})
     



 
  
