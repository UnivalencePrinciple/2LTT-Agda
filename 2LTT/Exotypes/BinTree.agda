{-# OPTIONS --without-K --two-level --cumulativity #-}

module 2LTT.Exotypes.BinTree where

open import 2LTT.Primitive
open import 2LTT.Exotypes.Naturals
open import 2LTT.Exotypes.Sigma
open import 2LTT.Exotypes.Unit
open import 2LTT.Exotypes.Exo_Equality
open import 2LTT.Exotypes.Functions
open import 2LTT.Exotypes.Pi

--Binary Trees with labeled vertices
data BinTreeᵉ {i j : Level}(N : UUᵉ i) (L : UUᵉ j) : UUᵉ (i ⊔ j) where
  leafᵉ : L → BinTreeᵉ N L
  nodeᵉ : BinTreeᵉ N L → N → BinTreeᵉ N L → BinTreeᵉ N L

--Binary Trees without labeled vertices
data UnL-BinTreeᵉ : UUᵉ lzero  where
  ul-leafᵉ : UnL-BinTreeᵉ
  ul-nodeᵉ : UnL-BinTreeᵉ → UnL-BinTreeᵉ → UnL-BinTreeᵉ
  
number-of-leaves : UnL-BinTreeᵉ → ℕᵉ
number-of-leaves ul-leafᵉ = oneᵉ
number-of-leaves (ul-nodeᵉ t t₁) = (add-ℕᵉ (number-of-leaves t) (number-of-leaves t₁))

number-of-nodes : UnL-BinTreeᵉ → ℕᵉ
number-of-nodes ul-leafᵉ = zeroᵉ
number-of-nodes (ul-nodeᵉ t t₁) = succᵉ (add-ℕᵉ (number-of-nodes t) (number-of-nodes t₁))

--We can turn an unlabeled binary tree into a labeled one

BinTree-to-UnLBinTree : {i j : Level}{N : UUᵉ i}{L : UUᵉ j} → BinTreeᵉ N L →
       Σᵉ (UnL-BinTreeᵉ) (λ t → (folded-×ᵉ (number-of-leaves t) L) ×ᵉ (folded-×ᵉ (number-of-nodes t) N))
BinTree-to-UnLBinTree  (leafᵉ x) = ul-leafᵉ ,ᵉ (x ,ᵉ starᵉ) ,ᵉ starᵉ
BinTree-to-UnLBinTree  (nodeᵉ t x t₁) =
  ul-nodeᵉ (pr1ᵉ (BinTree-to-UnLBinTree  t)) (pr1ᵉ (BinTree-to-UnLBinTree  t₁)) ,ᵉ
  add-folded-×ᵉ _ _ ((pr1ᵉ (pr2ᵉ (BinTree-to-UnLBinTree  t))) ,ᵉ (pr1ᵉ (pr2ᵉ (BinTree-to-UnLBinTree  t₁)))) ,ᵉ
  x ,ᵉ add-folded-×ᵉ _ _  ((pr2ᵉ (pr2ᵉ (BinTree-to-UnLBinTree t))) ,ᵉ (pr2ᵉ (pr2ᵉ (BinTree-to-UnLBinTree  t₁))))


UnLBinTree-to-BinTree' : {i j : Level}{N : UUᵉ i}{L : UUᵉ j} →
           (t : (UnL-BinTreeᵉ)) → (p : (folded-×ᵉ (number-of-leaves t) L) ×ᵉ (folded-×ᵉ (number-of-nodes t) N)) →
           BinTreeᵉ N L
UnLBinTree-to-BinTree' ul-leafᵉ  ((a ,ᵉ starᵉ) ,ᵉ starᵉ) = leafᵉ a 
UnLBinTree-to-BinTree' (ul-nodeᵉ t t₁) (p ,ᵉ b ,ᵉ q) =
  nodeᵉ
   (UnLBinTree-to-BinTree' t (pr1ᵉ (inv-add-folded-×ᵉ _ _ p) ,ᵉ pr1ᵉ (inv-add-folded-×ᵉ _ _ q)))
   b
   (UnLBinTree-to-BinTree' t₁ ((pr2ᵉ (inv-add-folded-×ᵉ _ _ p)) ,ᵉ pr2ᵉ (inv-add-folded-×ᵉ _ _ q)))

UnLBinTree-to-BinTree : {i j : Level}{N : UUᵉ i}{L : UUᵉ j} →
           Σᵉ (UnL-BinTreeᵉ) (λ t → (folded-×ᵉ (number-of-leaves t) L) ×ᵉ (folded-×ᵉ (number-of-nodes t) N)) →
           BinTreeᵉ N L
UnLBinTree-to-BinTree = (pr1ᵉ Πᵉ-Σ-expansion UnLBinTree-to-BinTree')


BinTree-to-UnLBinTree-sec : {i j : Level}{N : UUᵉ i}{L : UUᵉ j} →
           (t : UnL-BinTreeᵉ) (p : _×ᵉ_ {j} {i} (folded-×ᵉ (number-of-leaves t) L) (folded-×ᵉ (number-of-nodes t) N)) →
           BinTree-to-UnLBinTree (UnLBinTree-to-BinTree (t ,ᵉ p)) =ᵉ (t ,ᵉ p)
BinTree-to-UnLBinTree-sec ul-leafᵉ (a ,ᵉ starᵉ) = reflᵉ
BinTree-to-UnLBinTree-sec {i} {j} {N = N} {L = L} (ul-nodeᵉ t t₁)  (p ,ᵉ b ,ᵉ q) =
  exo-concat (exo-ap {i ⊔ j} {i ⊔ j} aux-map (pair-=ᵉ _ _ (path1 ,ᵉ path2)))
             (exo-ap {i ⊔ j} {i ⊔ j} (λ q →  _,ᵉ_ {lzero} {i ⊔ j}
                                                   (ul-nodeᵉ t t₁)
                                                   (_,ᵉ_ {j} {i} (pr1ᵉ {j} {i} q) (_,ᵉ_ {i} {i} b (pr2ᵉ q))))
               (pair-=ᵉ  _ _ (path3 ,ᵉ path4)))
  where
    TT = Σᵉ (UnL-BinTreeᵉ) (λ t → (folded-×ᵉ (number-of-leaves t) L) ×ᵉ (folded-×ᵉ (number-of-nodes t) N))
    aux-map : TT ×ᵉ TT → TT
    aux-map ((u1 ,ᵉ u2) ,ᵉ (v1 ,ᵉ v2)) =
      (ul-nodeᵉ u1 v1) ,ᵉ
      add-folded-×ᵉ _ _ ((pr1ᵉ u2) ,ᵉ (pr1ᵉ v2)) ,ᵉ
      b ,ᵉ add-folded-×ᵉ _ _ ((pr2ᵉ u2) ,ᵉ (pr2ᵉ v2))
    path1 = BinTree-to-UnLBinTree-sec t (pr1ᵉ (inv-add-folded-×ᵉ _ _ p) ,ᵉ pr1ᵉ (inv-add-folded-×ᵉ _ _ q))
    path2 = BinTree-to-UnLBinTree-sec t₁ (pr2ᵉ (inv-add-folded-×ᵉ _ _ p) ,ᵉ pr2ᵉ (inv-add-folded-×ᵉ _ _ q))
    path3 = add-folded-×ᵉ-sec (number-of-leaves t) (number-of-leaves t₁) p
    path4 = add-folded-×ᵉ-sec (number-of-nodes t) (number-of-nodes t₁) q



BinTree-to-UnLBinTree-retr : {i j : Level}{N : UUᵉ i}{L : UUᵉ j} →
           (p : BinTreeᵉ {i} {j} N L) → UnLBinTree-to-BinTree (BinTree-to-UnLBinTree p) =ᵉ p
BinTree-to-UnLBinTree-retr (leafᵉ x) = reflᵉ
BinTree-to-UnLBinTree-retr {i} {j} (nodeᵉ t x t₁) =
  exo-ap (λ s → nodeᵉ {i} {j} (pr1ᵉ {i ⊔ j} {i ⊔ j} s) x (pr2ᵉ s))
         (pair-=ᵉ _ _ (exo-concat (exo-ap UnLBinTree-to-BinTree (dep-pair-=ᵉ _ _ (reflᵉ ,ᵉ path1))) (BinTree-to-UnLBinTree-retr t) ,ᵉ
                       exo-concat (exo-ap UnLBinTree-to-BinTree (dep-pair-=ᵉ _ _ (reflᵉ ,ᵉ path2))) (BinTree-to-UnLBinTree-retr t₁)))
  where
   path1 = pair-=ᵉ _ _ (pr1ᵉ (inv-pair-=ᵉ _ _ (add-folded-×ᵉ-retr _ _
                              (pr1ᵉ (pr2ᵉ (BinTree-to-UnLBinTree t)) ,ᵉ pr1ᵉ (pr2ᵉ (BinTree-to-UnLBinTree t₁))))) ,ᵉ
                        (pr1ᵉ (inv-pair-=ᵉ _ _ (add-folded-×ᵉ-retr _ _
                              (pr2ᵉ (pr2ᵉ (BinTree-to-UnLBinTree t)) ,ᵉ pr2ᵉ (pr2ᵉ (BinTree-to-UnLBinTree t₁)))))))
   path2 = pair-=ᵉ _ _ (pr2ᵉ (inv-pair-=ᵉ _ _ (add-folded-×ᵉ-retr _ _
                              (pr1ᵉ (pr2ᵉ (BinTree-to-UnLBinTree t)) ,ᵉ pr1ᵉ (pr2ᵉ (BinTree-to-UnLBinTree t₁))))) ,ᵉ
                        (pr2ᵉ (inv-pair-=ᵉ _ _ (add-folded-×ᵉ-retr _ _
                              (pr2ᵉ (pr2ᵉ (BinTree-to-UnLBinTree t)) ,ᵉ pr2ᵉ (pr2ᵉ (BinTree-to-UnLBinTree t₁)))))))


BinTree-to-UnLBinTree-iso : {i j : Level}{N : UUᵉ i}{L : UUᵉ j} →
           Σᵉ (UnL-BinTreeᵉ) (λ t → (folded-×ᵉ (number-of-leaves t) L) ×ᵉ (folded-×ᵉ (number-of-nodes t) N)) ≅
           BinTreeᵉ N L
BinTree-to-UnLBinTree-iso = UnLBinTree-to-BinTree  ,ᵉ
                             (BinTree-to-UnLBinTree  ,ᵉ
                              ((λ { (t ,ᵉ p) → BinTree-to-UnLBinTree-sec t p}) ,ᵉ
                              BinTree-to-UnLBinTree-retr))

----------------------------------------------------------------------------
