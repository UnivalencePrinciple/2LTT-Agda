{-# OPTIONS --without-K --exact-split --two-level --cumulativity --type-in-type #-}

module 2LTT.Sharpness.On_Sharpness_of_Nat where

open import 2LTT.Sharpness.isSharp_equiv_definitions public

cofib-to-sharp-ℕᵉ : {i : Level} → isCofibrant ℕᵉ i → isSharp ℕᵉ i
isSharp.cofibrant-witness (cofib-to-sharp-ℕᵉ P) = P
isSharp.fibrant-replacement (cofib-to-sharp-ℕᵉ P) = ℕ
isSharp.fibrant-transfer (cofib-to-sharp-ℕᵉ P) = map-ℕᵉ
isSharp.precomp-is-equiv (cofib-to-sharp-ℕᵉ {i} P) Y
  = Lemma-2-3--2->1 {lzero} {i} ℕᵉ P ℕ map-ℕᵉ has-sec-proof Y
  where
    r = map-ℕᵉ

    aux-Π-type : Π ℕ (λ n → (Π (ℕ → UU i) (λ Y → (Π (fibrant-match (Π-fibrant-witness (P (Y ∘ᵉ r)))) (λ _ → Y n)))))
    aux-Π-type zero Y x = k x zeroᵉ
      where
        FM = fibrant-match (Π-fibrant-witness (P (Y ∘ᵉ r)))

        k : FM → Πᵉ ℕᵉ (Y ∘ᵉ r)
        k = pr1ᵉ (pr2ᵉ (fibrant-witness (Π-fibrant-witness (P (Y ∘ᵉ r)))))
    aux-Π-type (succ n) Y x = aux-Π-type n Y' (h' (λ u → k x (succᵉ u))) 
      where
        Y' : ℕ → UU i
        Y' n = Y (succ n)

        FM = fibrant-match (Π-fibrant-witness (P (Y ∘ᵉ r)))

        k : FM → Πᵉ ℕᵉ (Y ∘ᵉ r)
        k = pr1ᵉ (pr2ᵉ (fibrant-witness (Π-fibrant-witness (P (Y ∘ᵉ r)))))
            
        FM' = fibrant-match (Π-fibrant-witness (P (Y' ∘ᵉ r)))

        h' : Πᵉ ℕᵉ (Y' ∘ᵉ r) → FM'
        h' = pr1ᵉ (fibrant-witness (Π-fibrant-witness (P (Y' ∘ᵉ r))))

    aux-eq : (m : ℕᵉ) → (Π (ℕ → UU i)
             (λ Y → (Π (fibrant-match (Π-fibrant-witness (P (Y ∘ᵉ r))))
                        (λ x → Id (aux-Π-type (r m) Y x) ((pr1ᵉ (pr2ᵉ (fibrant-witness (Π-fibrant-witness (P (Y ∘ᵉ r)))))) x m)))))
    aux-eq zeroᵉ Y x = refl
    aux-eq (succᵉ m) Y x = aux-eq m Y' (h' (λ u → k x (succᵉ u))) ·
                            (=ᵉ-to-Id (happlyᵉ (kh' ((k x) ∘ᵉ succᵉ)) m) ·
                              refl)
      where
        Y' : ℕ → UU i
        Y' n = Y (succ n)

        FM = fibrant-match (Π-fibrant-witness (P (Y ∘ᵉ r)))

        k : FM → Πᵉ ℕᵉ (Y ∘ᵉ r)
        k = pr1ᵉ (pr2ᵉ (fibrant-witness (Π-fibrant-witness (P (Y ∘ᵉ r)))))
            
        FM' = fibrant-match (Π-fibrant-witness (P (Y' ∘ᵉ r)))

        h' : Πᵉ ℕᵉ (Y' ∘ᵉ r) → FM'
        h' = pr1ᵉ (fibrant-witness (Π-fibrant-witness (P (Y' ∘ᵉ r))))

        k' : FM' → Πᵉ ℕᵉ (Y' ∘ᵉ r)
        k' = pr1ᵉ (pr2ᵉ (fibrant-witness (Π-fibrant-witness (P (Y' ∘ᵉ r)))))

        kh' : (X : Πᵉ ℕᵉ (Y' ∘ᵉ r)) → k' (h' X) =ᵉ X
        kh' = pr1ᵉ (pr2ᵉ (pr2ᵉ (fibrant-witness (Π-fibrant-witness (P (Y' ∘ᵉ r))))))        
 
    has-sec-proof : (Y : ℕ → UU i) → Has-Section-Precomp ℕᵉ P ℕ map-ℕᵉ Y
    has-sec-proof Y = inv-map , inv-map-issec
      where
        FM = fibrant-match (Π-fibrant-witness (P (Y ∘ᵉ r)))
        hk = pr2ᵉ (pr2ᵉ (pr2ᵉ (fibrant-witness (Π-fibrant-witness (P (Y ∘ᵉ r))))))

        inv-map : (x : FM) → Π ℕ Y
        inv-map x n = aux-Π-type n Y x
        
        fib-precomp = Fib-map {i} {i} {Π ℕ Y} {Πᵉ ℕᵉ (Y ∘ᵉ r)}
                                                           (isfibrant _ ≅-refl)
                                                           (isCofibrant-at.Π-fibrant-witness (P (Y ∘ᵉ r)))
                                                           (precomp ℕᵉ ℕ r Y)
        inv-map-issec : (x : FM) → Id (fib-precomp (inv-map x)) x
        inv-map-issec x = FUNEXT.FEP {i} {i} {ℕᵉ} {Y ∘ᵉ r} {P} (λ m → aux-eq m Y x) · (=ᵉ-to-Id (hk x))
          
