{-# OPTIONS --without-K --exact-split --two-level --type-in-type #-}

module 2LTT_C.Sharpness.Sharpness_of_Sigma where

open import 2LTT_C.Sharpness.isSharp public
open import 2LTT_C.Coercion.Fibrant_Functions public

Σᵉ-preserve-Sharp : {i j k : Level}{A : UUᵉ i}{B : A → UUᵉ j}
                               → isSharp {i} A (lsuc j ⊔ k) → ((a : A) → isSharp {j} (B a) k)
                               → isSharp {i ⊔ j} (Σᵉ A B) k
Σᵉ-preserve-Sharp {i} {j} {k} {A} {B} P Q = issharp cwΣAB
                                                (Σ frA RB̃)
                                                ftΣ
                                                λ Y → precomp-equiv.proof {Y}
  where
   cwA : isCofibrant A (lsuc j ⊔ k)
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
              (isCofibrant-at.Π-fibrant-witness (cwA (λ _ → UU j)))
-------            
   F : C (frA → UU j) → (A → C (UU j))
   F = (precomp A (frA) (ftA) (λ _ → UU j))
   F' : (frA → UU j) → midset
   F' =  (Fib-map (isfibrant _ ≅-refl) (isCofibrant-at.Π-fibrant-witness (cwA (λ _ → UU j))) F)
-------
   pcmpeqA : (Y : frA → UU k)
                 → Fib-isEquiv (isfibrant _ ≅-refl) (isCofibrant-at.Π-fibrant-witness (cwA (λ x → Y (ftA x)))) (precomp {i} {k} A frA ftA Y)
   pcmpeqA = isSharp.precomp-is-equiv P
-------
   G : midset → (frA → UU j)
   G = pr1 (equivs-are-invertible F' (pcmpeqA (λ _ → UU j)))
-------
   GF : (G ∘ F') ~ id
   GF = pr1 (pr2 (equivs-are-invertible F' (pcmpeqA (λ _ → UU j))))
-------
   FG : (F' ∘ G) ~ id
   FG = pr2 (pr2 (equivs-are-invertible F' (pcmpeqA (λ _ → UU j))))
-------
   CWB : (a : A) → isCofibrant (B a) k
   CWB a = isSharp.cofibrant-witness (Q a)
-------
   cwΣAB : isCofibrant (Σᵉ A B) k
   cwΣAB = Σᵉ-preserve-Cofibrant cwA CWB
-------
   RB : (a : A) → UU j
   RB a = isSharp.fibrant-replacement (Q a)
-------
   FTB : (a : A) → ((B a) → (RB a))
   FTB a = isSharp.fibrant-transfer (Q a)
-------
   pcmpeqBa : (a : A) → (Y : (RB a) → UU k)
              → Fib-isEquiv (isfibrant _ ≅-refl)
                             (isCofibrant-at.Π-fibrant-witness ((CWB a) (λ x → Y ((FTB a) x))))
                             (precomp {j} {k} (B a) (RB a) (FTB a) Y)
   pcmpeqBa a = isSharp.precomp-is-equiv (Q a)
-------
   α : (A → C (UU j)) → C midset
   α = pr1ᵉ (isFibrant.fibrant-witness
                   (isCofibrant-at.Π-fibrant-witness (cwA (λ _ → UU j))))
-------
   β : C midset → (A → C (UU j))
   β = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness
                   (isCofibrant-at.Π-fibrant-witness (cwA (λ _ → UU j)))))
-------
   αβ : (x : _) → α (β x) =ᵉ x
   αβ = pr2ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness
                   (isCofibrant-at.Π-fibrant-witness (cwA (λ _ → UU j))))))
-------
   βα : (x : _) → β (α x) =ᵉ x
   βα = pr1ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness
                   (isCofibrant-at.Π-fibrant-witness (cwA (λ _ → UU j))))))
-------
   RB̃ : frA → UU j
   RB̃ = G (ic (α (λ a → c (RB a))))
-------
   ev : A → ((A → C (UU j)) → C (UU j))
   ev a Y = Y a
-------
   eṽ : A → (midset → C (UU j))
   eṽ a = (λ x → (ev a) λ a → (β (c x) a))
-------
   L1 : Id (ic (α (λ a → c (RB̃ (ftA a))))) (ic (α (λ a → c (RB a))))
   L1 = (ap F' {RB̃} {G (ic (α (λ a → c (RB a))))} refl) · FG (ic (α (λ a → c (RB a))))
-------
   L2 : (a : A) → (Id (RB̃ (ftA a)) (RB a))
   L2 a = (=ᵉ-to-Id (exo-ap {i ⊔ lsuc j} {lsuc j} (ev a) (βα (λ a' → c (RB̃ (ftA a')))))) ⁻¹
           · (ap (λ x → ic (eṽ a x)) L1 
             · =ᵉ-to-Id (exo-ap {i ⊔ lsuc j} {lsuc j} (ev a) (βα (λ a → c (RB a))))) 
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
   EQ-T-lhtp : (a : A) → ((EQ-T a) ∘ (EQ-T' a)) ~ id
   EQ-T-lhtp a = pr1 (pr2 (equivs-are-invertible _ (pr2 (idtoeqv (L2 a)))))
-------
   EQ-T-rhtp : (a : A) → ((EQ-T' a) ∘ (EQ-T a)) ~ id
   EQ-T-rhtp a = pr2 (pr2 (equivs-are-invertible _ (pr2 (idtoeqv (L2 a)))))
-------
   EQ-T-isEquiv : (a : A) → isEquiv (EQ-T a)
   EQ-T-isEquiv a = invertibles-are-equiv _ ((EQ-T' a) , (EQ-T-rhtp a) , (EQ-T-lhtp a))
-------
   ftΣ : (Σᵉ A B) → (Σ frA (λ x → RB̃ x))
   ftΣ = (λ x → ftA (pr1ᵉ x) , (EQ-T (pr1ᵉ x)) ((FTB (pr1ᵉ x)) (pr2ᵉ x)))
-------
   module precomp-equiv {Y : Σ {i} {j} frA (λ x → RB̃ x) → UU k} where
        ----We'll use the idea in the UP paper, page 19. There is a chain of
        ----equivalences that contains six Π-types. We'll enumerate these accordingly.
        ----Also, we'll enumerate the maps between these Π-types according to their inputs.
        ΠType-1 : UU (i ⊔ j ⊔ k) --this is fibrant by default.
        ΠType-1 = Π (Σ frA RB̃) Y
        -------------------------
        ΠType-2 : UU (i ⊔ j ⊔ k) --this is fibrant by default.
        ΠType-2 = Π frA (λ x → Π (RB̃ x) (λ y → Y (x , y)))
        -------------------------
        Map-1 : C ΠType-1 → C ΠType-2 --there is an obvious equivalence between them.
        Map-1 = λ {(c T) → c (Π-Σ-expansion T)}
        -------------------------
        ΠType-3 : UUᵉ (i ⊔ j ⊔ k) --this is an exo-type, but fibrant one.
        ΠType-3 = Πᵉ A (λ a → C (Π (RB̃ (ftA a)) (λ y → Y ((ftA a) , y))))
        -------------------------
        Fibrant3 : isFibrant ΠType-3
        Fibrant3 = (isCofibrant-at.Π-fibrant-witness (cwA (λ a → Π (RB̃ (ftA a)) (λ y → Y ((ftA a) , y)))))
        -------------------------
        Map-2 : C ΠType-2 → ΠType-3
        Map-2 (c T) = λ a → c (λ y → T (ftA a) y) 
        -------------------------
        ΠType-4 : UUᵉ (i ⊔ j ⊔ k) --this is an exo-type, but fibrant one.
        ΠType-4 = Πᵉ A (λ a → C (Π (RB a) (λ y → Y ((ftA a) , EQ-T a y))))
        -------------------------
        Fibrant4 : isFibrant ΠType-4
        Fibrant4 = (isCofibrant-at.Π-fibrant-witness (cwA (λ a → Π (RB a) (λ y → Y ((ftA a) , EQ-T a y)))))
        -------------------------
        midmap : (a : A) → (Π (RB̃ (ftA a)) (λ y → Y ((ftA a) , y))) → (Π (RB a) (λ y → Y ((ftA a) , EQ-T a y)))
        midmap a = Π-functor (EQ-T a) (λ b → id)
        -------------------------
        Map-3 : ΠType-3 → ΠType-4
        Map-3 T = λ x → c (λ y → (midmap x) (ic (T x)) y)
        -------------------------
        ΠType-5 : UUᵉ (i ⊔ j ⊔ k) --this is an exo-type, but fibrant one.
        ΠType-5 = Πᵉ A (λ a → Πᵉ (B a) (λ b → C (Y ((ftA a) , EQ-T a (FTB a b)))))
        -------------------------
        Fibrant5 : isFibrant ΠType-5
        Fibrant5 = (isFibrant-iso (≅-sym {i ⊔ j ⊔ k}{i ⊔ j ⊔ k} Πᵉ-Σ-expansion)
                                (isCofibrant-at.Π-fibrant-witness (cwΣAB (λ x → Y (ftΣ x)))))
        -------------------------
        midmap' : (a : A) → C (Π (RB a) (λ y → Y ((ftA a) , EQ-T a y))) → (Πᵉ (B a) (λ b → C (Y ((ftA a) ,  EQ-T a (FTB a b)))))
        midmap' a = precomp (B a) (RB a) (FTB a) (λ y → Y ((ftA a) , EQ-T a y))
        -------------------------
        check-map : (a : A) → (Π (RB a) (λ y → Y ((ftA a) , EQ-T a y)))
                         → isFibrant.fibrant-match (isCofibrant-at.Π-fibrant-witness ((CWB a) (λ b → Y ((ftA a) ,  EQ-T a (FTB a b))))) 
        check-map a = Fib-map (isfibrant _ ≅-refl)
                              (isCofibrant-at.Π-fibrant-witness ((CWB a) (λ b → Y ((ftA a) ,  EQ-T a (FTB a b)))))                                                         (midmap' a)
        -------------------------
        midmap'-Fib-isEquiv : (a : A) → Fib-isEquiv (isfibrant _ ≅-refl)
                                                     (isCofibrant-at.Π-fibrant-witness ((CWB a) (λ b → Y ((ftA a) ,  EQ-T a (FTB a b)))))                                                         (midmap' a)
        midmap'-Fib-isEquiv a = (pcmpeqBa a) (λ y → Y ((ftA a) ,  EQ-T a y)) 
        -------------------------
        Map-4 : ΠType-4 → ΠType-5
        Map-4 = (Πᵉ-functor {i} {j ⊔ k} idᵉ midmap') 
        -------------------------
        ΠType-6 : UUᵉ (i ⊔ j ⊔ k) --this is an exo-type, but fibrant one.
        ΠType-6 = Πᵉ (Σᵉ A B) (λ z → C (Y (ftΣ z)))
        -------------------------
        Fibrant6 : isFibrant ΠType-6
        Fibrant6 = (isCofibrant-at.Π-fibrant-witness (cwΣAB (λ x → Y (ftΣ x))))
        -------------------------
        Map-5 : ΠType-5 → ΠType-6
        Map-5 = pr1ᵉ Πᵉ-Σ-expansion
        -------------------------
        Map-main : C ΠType-1 → ΠType-6
        Map-main = precomp (Σᵉ A B) (Σ frA RB̃) (ftΣ) Y
        -------------------------
        Main-Htp : (T : _) → Map-5 (Map-4 (Map-3 (Map-2 (Map-1 T)))) =ᵉ Map-main T
        Main-Htp T = reflᵉ
        -------------------------
        Equiv-1 : Fib-isEquiv (isfibrant _ ≅-refl) (isfibrant _ ≅-refl) Map-1
        Equiv-1 = Π-Σ-expansion-is-equiv
        -------------------------
        Equiv-2 : Fib-isEquiv (isfibrant _ ≅-refl) Fibrant3 Map-2
        Equiv-2 = pcmpeqA (λ x → Π (RB̃ x) (λ y → Y (x , y)))
        -------------------------
        Equiv-3 : Fib-isEquiv Fibrant3 Fibrant4 Map-3
        Equiv-3 = Fib-Π-functor-isEquiv {i} {j ⊔ k} cwA λ a → pr2 (Π-iso-cong {j} {k} (EQ-T a) {EQ-T-isEquiv a}
                                                                                       (λ b → id) {λ b → id-is-equiv})
        -------------------------
        Equiv-4 : Fib-isEquiv Fibrant4 Fibrant5 Map-4
        Equiv-4 = Fib-Π-functor-isEquiv {i} {j ⊔ k} {F = check-map} cwA λ a → (midmap'-Fib-isEquiv a)
        -------------------------
        Equiv-5 : Fib-isEquiv Fibrant5 Fibrant6 Map-5
        Equiv-5 = Iso-to-Fib-isEquiv Fibrant5 Fibrant6 (pr1ᵉ Πᵉ-Σ-expansion) (pr2ᵉ Πᵉ-Σ-expansion)
        -------------------------
        Equiv-main : Fib-isEquiv (isfibrant ΠType-1 ≅-refl) Fibrant6 (Map-5 ∘ᵉ (Map-4 ∘ᵉ (Map-3 ∘ᵉ (Map-2 ∘ᵉ Map-1))))
        Equiv-main = Fib-comp-isEquiv {i ⊔ j ⊔ k}{i ⊔ j ⊔ k} {i ⊔ j ⊔ k} (isfibrant _ ≅-refl)
                                      Fibrant5
                                      Fibrant6
                                      (Map-4 ∘ᵉ (Map-3 ∘ᵉ (Map-2 ∘ᵉ Map-1))) Map-5
                                      (Fib-comp-isEquiv {i ⊔ j ⊔ k}{i ⊔ j ⊔ k} {i ⊔ j ⊔ k} (isfibrant _ ≅-refl)
                                      Fibrant4
                                      Fibrant5
                                      (Map-3 ∘ᵉ (Map-2 ∘ᵉ Map-1)) Map-4
                                      (Fib-comp-isEquiv {i ⊔ j ⊔ k}{i ⊔ j ⊔ k} {i ⊔ j ⊔ k} (isfibrant _ ≅-refl)
                                      Fibrant3
                                      Fibrant4
                                      (Map-2 ∘ᵉ Map-1) Map-3
                                      (Fib-comp-isEquiv (isfibrant _ ≅-refl)
                                      (isfibrant _ ≅-refl)
                                      Fibrant3
                                      Map-1 Map-2
                                      Equiv-1
                                      Equiv-2)
                                      Equiv-3)
                                      Equiv-4)
                                      Equiv-5
        -------------------------
        proof : Fib-isEquiv (isfibrant _ ≅-refl) Fibrant6 Map-main
        proof = Fib-htpy-to-isEquiv (isfibrant _ ≅-refl)
                                    Fibrant6
                                    (Map-5 ∘ᵉ (Map-4 ∘ᵉ (Map-3 ∘ᵉ (Map-2 ∘ᵉ Map-1))))
                                    Map-main
                                    Main-Htp
                                    Equiv-main
