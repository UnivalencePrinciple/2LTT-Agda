{-# OPTIONS --without-K --exact-split --two-level --cumulativity #-}

module 2LTT.Sharpness.On_Sharpness_of_List where

open import 2LTT.Sharpness.isSharp_equiv_definitions public
open import 2LTT.Sharpness.On_Sharpness_of_Nat public

cofib-list-to-sharp-List : {l1 l2 : Level}(A : UUᵉ l1) → isSharp A (l1 ⊔ l2) → isCofibrant ℕᵉ (l1 ⊔ l2) → isSharp (Listᵉ A) l2
cofib-list-to-sharp-List {l1} {l2} A P R
  = issharp Q (List RA) rList (Lemma-2-3--2->1 {l1} {l2} (Listᵉ {l1} A) Q (List {l1} RA) rList has-sec-proof)
  where
   cwA = isSharp.cofibrant-witness P

   Q = List-isCofibrant {l1} {l2} A cwA R 

   RA = isSharp.fibrant-replacement P

   rA : A → RA
   rA = isSharp.fibrant-transfer P

   rList : Listᵉ A → List RA
   rList nilᵉ = nil
   rList (consᵉ x l) = cons (rA x) (rList l)

   FM : (Y : List RA → UU l2) → UU (l1 ⊔ l2)
   FM Y = (fibrant-match (Π-fibrant-witness (Q (Y ∘ᵉ rList))))

   k : (Y : List RA → UU l2) → FM Y → Πᵉ (Listᵉ A) (Y ∘ᵉ rList)
   k Y = pr1ᵉ (pr2ᵉ ((fibrant-witness (Π-fibrant-witness (Q (Y ∘ᵉ rList))))))

   h : (Y : List RA → UU l2) → Πᵉ (Listᵉ A) (Y ∘ᵉ rList) → FM Y
   h Y = pr1ᵉ ((fibrant-witness (Π-fibrant-witness (Q (Y ∘ᵉ rList)))))

   kh = λ Y → pr1ᵉ (pr2ᵉ (pr2ᵉ ((fibrant-witness (Π-fibrant-witness (Q (Y ∘ᵉ rList)))))))
   hk = λ Y → pr2ᵉ (pr2ᵉ (pr2ᵉ ((fibrant-witness (Π-fibrant-witness (Q (Y ∘ᵉ rList)))))))

   aux-type : (s : List {l1} RA) → (Y : List RA → UU l2) → (x : FM Y) → Y (s)
   aux-type nil Y x = (k Y) x nilᵉ
   aux-type (cons c l) Y x = aux-type l Y' ((h Y') T )
    where
     Y' : List RA → UU l2
     Y' l' = Y (cons c l')

     T : (l' : Listᵉ A) → Y' (rList l')
     T l' = β (u λ a → (k Y) x (consᵉ a l') ) c
       where
         equiv = (isSharp.precomp-is-equiv P) (λ z → Y (cons z (rList l')))
         u = pr1ᵉ ((fibrant-witness (Π-fibrant-witness (cwA ((λ z → Y (cons z (rList l'))) ∘ᵉ rA)))))
         β = pr1 (equivs-are-invertible _ equiv)

   aux-eq : (t : Listᵉ A) → (Y : List RA → UU l2) → (x : FM Y) →
            Id (aux-type (rList t) Y x) ((k Y) x t)
   aux-eq nilᵉ Y x = refl
   aux-eq (consᵉ b t) Y x = refl · ((aux-eq t Y' ((h Y') T)) · ((=ᵉ-to-Id (happlyᵉ ((kh Y') T) t)) · q t))
     where
       Y' : List RA → UU l2
       Y' l' = Y (cons (rA b) l')

       T : (l' : Listᵉ A) → Y' (rList l')
       T l' = β (u (λ a → (k Y) x (consᵉ a l'))) (rA b)
         where
           equiv = (isSharp.precomp-is-equiv P) (λ z → Y (cons z (rList l')))
           u = pr1ᵉ ((fibrant-witness (Π-fibrant-witness (cwA ((λ z → Y (cons z (rList l'))) ∘ᵉ rA)))))
           β = pr1 (equivs-are-invertible _ equiv)

       q : (l' : Listᵉ A) → Id (T l') (k Y x (consᵉ b l'))
       q l' = (=ᵉ-to-Id (happlyᵉ {l1} {l2} (vu ((β (u (λ a → (k Y) x (consᵉ a l')))) ∘ᵉ rA)) b)) ⁻¹ ·
                (ap (λ f → (v f) b) (αβ (u (λ a → (k Y) x (consᵉ a l')))) ·
                  =ᵉ-to-Id (happlyᵉ {l1} {l2} (vu (λ a → (k Y) x (consᵉ a l'))) b))
         where
           equiv = (isSharp.precomp-is-equiv P) (λ z → Y (cons z (rList l')))
           u = pr1ᵉ ((fibrant-witness (Π-fibrant-witness (cwA ((λ z → Y (cons z (rList l'))) ∘ᵉ rA)))))
           v = pr1ᵉ (pr2ᵉ ((fibrant-witness (Π-fibrant-witness (cwA ((λ z → Y (cons z (rList l'))) ∘ᵉ rA))))))
           vu = pr1ᵉ (pr2ᵉ (pr2ᵉ ((fibrant-witness (Π-fibrant-witness (cwA ((λ z → Y (cons z (rList l'))) ∘ᵉ rA)))))))
           β = pr1 (equivs-are-invertible _ equiv)
           αβ = pr2 (pr2 (equivs-are-invertible _ equiv))

   has-sec-proof : (Y : List {l1} RA → UU l2) → Has-Section-Precomp {l1} {l2} (Listᵉ A) Q (List RA) rList Y
   has-sec-proof Y = inv-map , inv-map-issec
      where
        inv-map : (x : FM Y) → Π (List RA) Y
        inv-map x l = aux-type l Y x
        
        fib-precomp = Fib-map {l1 ⊔ l2} {l1 ⊔ l2} {A = Π (List {l1} RA) Y} {B = Πᵉ (Listᵉ A) (Y ∘ᵉ rList)}
                                                           (isfibrant _ ≅-refl)
                                                           (isCofibrant-at.Π-fibrant-witness (Q (Y ∘ᵉ rList)))
                                                           (precomp (Listᵉ {l1} A) (List RA) rList Y)
        inv-map-issec : (x : FM Y) → Id (fib-precomp (inv-map x)) x
        inv-map-issec x = FUNEXT.FEP {A = Listᵉ A} {B = Y ∘ᵉ rList} {P = Q} (λ l → aux-eq l Y x) · (=ᵉ-to-Id ((hk Y) x))
