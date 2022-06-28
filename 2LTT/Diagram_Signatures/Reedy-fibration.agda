{-# OPTIONS --without-K --exact-split --two-level  --cumulativity #-}

module 2LTT.Diagram_Signatures.Reedy-fibration where

open import 2LTT.Diagram_Signatures.Definition public

module _
   {i j k : Level}{ℒ : Inv-Exo-cat i j}
   {M : Exo-Functor {i} {j} {lsuc k} {k} (iexo-cat ℒ) (ExoUniv-is-Exo-cat k)}
   {n : ℕᵉ}{K : ℒ ⟅ n ⟆}
   where

   Cat-ℒ = iexo-cat ℒ
   M0 = (Obj-map Cat-ℒ ((ExoUniv-is-Exo-cat k)) M)
   M1 = (Arrow-map Cat-ℒ ((ExoUniv-is-Exo-cat k)) M)
   
   matching-property : (d : (m : ℕᵉ) (p : m <ᵉ n) (L : Fanout {ℒ = ℒ} n K m p) →
                       (M0 (pr1ᵉ (pr1ᵉ L)))) →  UUᵉ (lsuc (i ⊔ j ⊔ k))
   matching-property d = (m1 m2 : ℕᵉ) (m1<m2 : succᵉ m1 ≤ᵉ m2) (m2<n : succᵉ m2 ≤ᵉ n) →
                         ((L1 ,ᵉ f1) : Fanout {ℒ = ℒ} n K m1 (<ᵉ-trans m2<n m1<m2)) →
                         ((L2 ,ᵉ f2) : Fanout {ℒ = ℒ} n K m2 m2<n) →
                            Πᵉ {j} {j ⊔ k} (Cat-ℒ [ (pr1ᵉ L1) , (pr1ᵉ L2) ])
                               (λ g → (f2 =ᵉ (g ○⟨ Cat-ℒ ⟩ f1)) →
                               M1 g ((d m1 (<ᵉ-trans m2<n m1<m2) (L1 ,ᵉ f1)))
                                 =ᵉ
                               (d m2 m2<n (L2 ,ᵉ f2)))

   matching-object : UUᵉ (lsuc (i ⊔ j ⊔ k))
   matching-object = Σᵉ ((m : ℕᵉ) (p : m <ᵉ n) (L : Fanout {ℒ = ℒ} n K m p) → (M0 (pr1ᵉ (pr1ᵉ L))))
                       (λ d → matching-property d)


   Reedy-map : (M0 (pr1ᵉ K)) → matching-object
   Reedy-map x = (λ m p → λ {(L ,ᵉ f) → M1 f x}) ,ᵉ
                 λ m1 m2 m1<m2 m2<n → λ { (L1 ,ᵉ f1) → λ { (L2 ,ᵉ f2) → λ g p →
                 exo-concat (happlyᵉ (exo-inv (pr2ᵉ (pr2ᵉ (pr2ᵉ M)))) x)
                            (exo-ap (λ h → M1 h x) (exo-inv p)) }}

   is-Reedy-fibrant : UUᵉ (lsuc (lsuc (i ⊔ j ⊔  k)))
   is-Reedy-fibrant = (n : ℕᵉ) (K : ℒ ⟅ n ⟆) →
                     isFibration {k} {lsuc (i ⊔ j ⊔ k)} (Reedy-map) 



--Properties
--Ex. 4.10. If K has rank 0, then matching object at K is equivalent to unit type.
match-obj-zero-sort-≅-⊤ᵉ : {i j k : Level}{ℒ : Inv-Exo-cat i j}
                           {M : Exo-Functor {i} {j} {lsuc k} {k} (iexo-cat ℒ) (ExoUniv-is-Exo-cat k)}
                           (K : ℒ ⟅ zeroᵉ ⟆) → matching-object {i} {j} {k} {ℒ} {M} {zeroᵉ} {K} ≅ ⊤ᵉ
match-obj-zero-sort-≅-⊤ᵉ {i} {j} {k} {ℒ} {M} K = (λ a → starᵉ) ,ᵉ
                                                 (λ b → ((λ m → λ {()}) ,ᵉ λ m1 m2 m1<m2 → λ {()})) ,ᵉ
                                                 (λ a → dep-pair-=ᵉ _ _
                                                      ((funextᵉ {_} {i ⊔ j ⊔ k} λ x → funextᵉ {_} {i ⊔ j ⊔ k} λ {()}) ,ᵉ
                                                       (funextᵉ {_} {i ⊔ j ⊔ k} λ x → funextᵉ {_} {i ⊔ j ⊔ k}
                                                          λ x₁ → funextᵉ {_} {i ⊔ j ⊔ k} λ x₂ → funextᵉ {_} {i ⊔ j ⊔ k} λ {()}))) ,ᵉ
                                                 (λ b → reflᵉ)                           
                      
