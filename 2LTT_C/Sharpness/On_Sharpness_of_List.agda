{-# OPTIONS --without-K --exact-split --two-level --type-in-type #-}

module 2LTT_C.Sharpness.On_Sharpness_of_List where

open import 2LTT_C.Sharpness.isSharp_equiv_definitions public
open import 2LTT_C.Sharpness.On_Sharpness_of_Nat public

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
   rList []ᵉ = []
   rList (x ::ᵉ l) = (rA x) :: (rList l)

   FM : (Y : List RA → UU l2) → UU (l1 ⊔ l2)
   FM Y = (fibrant-match (Π-fibrant-witness (Q (λ x → Y (rList x)))))

   k : (Y : List {l1} RA → UU l2) → C (FM Y) → Πᵉ (Listᵉ A) (λ x → C (Y (rList x)))
   k Y = pr1ᵉ (pr2ᵉ ((fibrant-witness (Π-fibrant-witness (Q (λ x → Y (rList x)))))))

   h : (Y : List {l1} RA → UU l2) → Πᵉ (Listᵉ A) (λ x → C (Y (rList x))) → C (FM Y)
   h Y = pr1ᵉ ((fibrant-witness (Π-fibrant-witness (Q (λ x → Y (rList x))))))

   kh = λ Y → pr1ᵉ (pr2ᵉ (pr2ᵉ ((fibrant-witness (Π-fibrant-witness (Q (λ x → Y (rList x))))))))
   hk = λ Y → pr2ᵉ (pr2ᵉ (pr2ᵉ ((fibrant-witness (Π-fibrant-witness (Q (λ x → Y (rList x))))))))

   aux-type : (s : List {l1} RA) → (Y : List RA → UU l2) → (x : FM Y) → Y (s)
   aux-type [] Y x = ic ((k Y) (c x) []ᵉ)
   aux-type (d :: l) Y x = aux-type l Y' (ic ((h Y') (λ x → c (T x))))
    where
     Y' : List RA → UU l2
     Y' l' = Y (d :: l')

     T : (l' : Listᵉ A) → Y' (rList l')
     T l' = β (ic (u λ a → (k Y) (c x) (a ::ᵉ l') )) d
       where
         equiv = (isSharp.precomp-is-equiv P) (λ z → Y (z :: (rList l')))
         u = pr1ᵉ ((fibrant-witness (Π-fibrant-witness (cwA (λ a → (λ z → Y (z :: (rList l'))) (rA a))))))
         β = pr1 (equivs-are-invertible _ equiv)

   aux-eq : (t : Listᵉ A) → (Y : List RA → UU l2) → (x : FM Y) →
            Id (aux-type (rList t) Y x) (ic ((k Y) (c x) t))
   aux-eq []ᵉ Y x = refl
   aux-eq (b ::ᵉ t) Y x = ((aux-eq t Y' (ic ((h Y') (λ x → c (T x)))))
                           · ((=ᵉ-to-Id (happlyᵉ ((kh Y') (λ x → c (T x))) t)) · q t))
     where
       Y' : List RA → UU l2
       Y' l' = Y ((rA b) :: l')

       T : (l' : Listᵉ A) → Y' (rList l')
       T l' = β (ic (u (λ a → (k Y) (c x) (a ::ᵉ l')))) (rA b)
         where
           equiv = (isSharp.precomp-is-equiv P) (λ z → Y (z :: (rList l')))
           u = pr1ᵉ ((fibrant-witness (Π-fibrant-witness (cwA (λ a → (λ z → Y (z :: (rList l'))) (rA a))))))
           β = pr1 (equivs-are-invertible _ equiv)

       q : (l' : Listᵉ A) → Id (T l') (ic (k Y (c x) (b ::ᵉ l')))
       q l' = (=ᵉ-to-Id (happlyᵉ {l1} {l2} (vu (λ a → c ((β (ic (u (λ a → (k Y) (c x) (a ::ᵉ l'))))) (rA a)))) b)) ⁻¹
                · (ap (λ f → ic ((v (c f)) b)) (αβ (ic (u (λ a → (k Y) (c x) (a ::ᵉ l')))))
                  · =ᵉ-to-Id (happlyᵉ {l1} {l2} (vu (λ a → (k Y) (c x) (a ::ᵉ l'))) b))
         where
           equiv = (isSharp.precomp-is-equiv P) (λ z → Y (z :: (rList l')))
           u = pr1ᵉ ((fibrant-witness (Π-fibrant-witness (cwA (λ a → (λ z → Y (z :: (rList l'))) (rA a))))))
           v = pr1ᵉ (pr2ᵉ ((fibrant-witness (Π-fibrant-witness (cwA (λ a → (λ z → Y (z :: (rList l'))) (rA a)))))))
           vu = pr1ᵉ (pr2ᵉ (pr2ᵉ ((fibrant-witness (Π-fibrant-witness (cwA (λ a → (λ z → Y (z :: (rList l'))) (rA a))))))))
           β = pr1 (equivs-are-invertible _ equiv)
           αβ = pr2 (pr2 (equivs-are-invertible _ equiv))

   has-sec-proof : (Y : List {l1} RA → UU l2) → Has-Section-Precomp {l1} {l2} (Listᵉ A) Q (List RA) rList Y
   has-sec-proof Y = inv-map , inv-map-issec
      where
        inv-map : (x : FM Y) → Π (List RA) Y
        inv-map x l = aux-type l Y x
        
        fib-precomp = Fib-map {l1 ⊔ l2} {l1 ⊔ l2} {A = C (Π (List {l1} RA) Y)} {B = Πᵉ (Listᵉ A) (λ x → C (Y (rList x)))}
                                                           (isfibrant _ ≅-refl)
                                                           (isCofibrant-at.Π-fibrant-witness (Q (λ x → Y (rList x))))
                                                           (precomp (Listᵉ {l1} A) (List RA) rList Y)
        inv-map-issec : (x : FM Y) → Id (fib-precomp (inv-map x)) x
        inv-map-issec x = FUNEXT.FEP {A = Listᵉ A} {B = λ x → Y (rList x)} {P = Q} (λ l → aux-eq l Y x) · (=ᵉ-to-Id ((hk Y) (c x)))
