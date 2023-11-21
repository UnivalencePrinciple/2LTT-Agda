{-# OPTIONS --without-K --exact-split --two-level --type-in-type #-}

module 2LTT_C.Sharpness.On_Sharpness_of_Nat where

open import 2LTT_C.Sharpness.isSharp_equiv_definitions public

cofib-to-sharp-ℕᵉ : {i : Level} → isCofibrant ℕᵉ i → isSharp ℕᵉ i
isSharp.cofibrant-witness (cofib-to-sharp-ℕᵉ P) = P
isSharp.fibrant-replacement (cofib-to-sharp-ℕᵉ P) = ℕ
isSharp.fibrant-transfer (cofib-to-sharp-ℕᵉ P) = map-ℕᵉ
isSharp.precomp-is-equiv (cofib-to-sharp-ℕᵉ {i} P) Y
  = Lemma-2-3--2->1 {lzero} {i} ℕᵉ P ℕ map-ℕᵉ has-sec-proof Y
  where
    r = map-ℕᵉ

    aux-Π-type : Π ℕ (λ n → (Π (ℕ → UU i) (λ Y → (Π (fibrant-match (Π-fibrant-witness (P (λ x → Y (r x))))) (λ _ → Y n)))))
    aux-Π-type zero Y x = ic (k (c x) zeroᵉ)
      where
        FM = fibrant-match (Π-fibrant-witness (P (λ x → Y (r x))))

        k : C FM → Πᵉ ℕᵉ  (λ x → C (Y (r x)))
        k = pr1ᵉ (pr2ᵉ (fibrant-witness (Π-fibrant-witness (P (λ x → Y (r x))))))
    aux-Π-type (succ n) Y x = (aux-Π-type n Y' (ic (h' (λ u → k (c x) (succᵉ u))))) 
      where
        Y' : ℕ → UU i
        Y' n = Y (succ n)

        FM = fibrant-match (Π-fibrant-witness (P  (λ x → Y (r x))))

        k : C FM → Πᵉ ℕᵉ  (λ x → C (Y (r x)))
        k = pr1ᵉ (pr2ᵉ (fibrant-witness (Π-fibrant-witness (P  (λ x → Y (r x))))))
            
        FM' = fibrant-match (Π-fibrant-witness (P  (λ x → Y' (r x))))

        h' : Πᵉ ℕᵉ  (λ x → C (Y' (r x))) → C FM'
        h' = pr1ᵉ (fibrant-witness (Π-fibrant-witness (P  (λ x → Y' (r x)))))

    aux-eq : (m : ℕᵉ) → (Π (ℕ → UU i)
             (λ Y → (Π (fibrant-match (Π-fibrant-witness (P  (λ x → Y (r x)))))
               (λ x → Id (aux-Π-type (r m) Y x) (ic ((pr1ᵉ (pr2ᵉ (fibrant-witness (Π-fibrant-witness (P  (λ x → Y (r x))))))) (c x) m))))))
    aux-eq zeroᵉ Y x = refl
    aux-eq (succᵉ m) Y x = aux-eq m Y' (ic (h' (λ u → k (c x) (succᵉ u))))
                            · =ᵉ-to-Id (happlyᵉ (kh' ((k (c x)) ∘ᵉ succᵉ)) m)
      where
        Y' : ℕ → UU i
        Y' n = Y (succ n)

        FM = fibrant-match (Π-fibrant-witness (P  (λ x → Y (r x))))

        k : C FM → Πᵉ ℕᵉ  (λ x → C (Y (r x)))
        k = pr1ᵉ (pr2ᵉ (fibrant-witness (Π-fibrant-witness (P  (λ x → Y (r x))))))
            
        FM' = fibrant-match (Π-fibrant-witness (P  (λ x → Y' (r x))))

        h' : Πᵉ ℕᵉ  (λ x → C (Y' (r x))) → C FM'
        h' = pr1ᵉ (fibrant-witness (Π-fibrant-witness (P  (λ x → Y' (r x)))))

        k' : C FM' → Πᵉ ℕᵉ  (λ x → C (Y' (r x)))
        k' = pr1ᵉ (pr2ᵉ (fibrant-witness (Π-fibrant-witness (P  (λ x → Y' (r x))))))

        kh' : (X : Πᵉ ℕᵉ  (λ x → C (Y' (r x)))) → k' (h' X) =ᵉ X
        kh' = pr1ᵉ (pr2ᵉ (pr2ᵉ (fibrant-witness (Π-fibrant-witness (P  (λ x → Y' (r x)))))))        
 
    has-sec-proof : (Y : ℕ → UU i) → Has-Section-Precomp ℕᵉ P ℕ map-ℕᵉ Y
    has-sec-proof Y = inv-map , inv-map-issec
      where
        FM = fibrant-match (Π-fibrant-witness (P  (λ x → Y (r x))))
        hk = pr2ᵉ (pr2ᵉ (pr2ᵉ (fibrant-witness (Π-fibrant-witness (P  (λ x → Y (r x)))))))

        inv-map : (x : FM) → Π ℕ Y
        inv-map x n = aux-Π-type n Y x
        
        fib-precomp = Fib-map {i} {i} {C (Π ℕ Y)} {Πᵉ ℕᵉ  (λ x → C (Y (r x)))}
                                                           (isfibrant _ ≅-refl)
                                                           (isCofibrant-at.Π-fibrant-witness (P  (λ x → Y (r x))))
                                                           (precomp ℕᵉ ℕ r Y)
        inv-map-issec : (x : FM) → Id (fib-precomp (inv-map x)) x
        inv-map-issec x = FUNEXT.FEP {i} {i} {ℕᵉ} {λ x → Y (r x)} {P} (λ m → aux-eq m Y x) · (=ᵉ-to-Id (hk (c x)))
          
