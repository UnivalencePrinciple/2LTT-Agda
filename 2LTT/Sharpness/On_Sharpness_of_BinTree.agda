{-# OPTIONS --without-K --exact-split --two-level --cumulativity --type-in-type #-}

module 2LTT.Sharpness.On_Sharpness_of_BinTree where

open import 2LTT.Sharpness.isSharp_equiv_definitions public
open import 2LTT.Sharpness.On_Sharpness_of_List
open import 2LTT.Sharpness.Sharpness_of_Fibrant_Types
open import 2LTT.Sharpness.Sharpness_of_Exo_Empty
open import 2LTT.Sharpness.Sharpness_of_Sigma
open import 2LTT.Sharpness.Properties
open import 2LTT.Sharpness.Sharpness_of_Finite_Types
open import 2LTT.Sharpness.Sharpness_of_Product 

--Multiple product of sharp exo-types is sharp
folded-×-sharp : {i j : Level} {A : UUᵉ i} → (isSharp {i} A (i ⊔ j)) → (n : ℕᵉ) → (isSharp {i} (folded-×ᵉ {i} n A) j)
folded-×-sharp {i} {j} P zeroᵉ = is-⊤ᵉ-Sharp {i} j
folded-×-sharp {i} {j} P (succᵉ n) = ×ᵉ-preserve-Sharp P (folded-×-sharp P n)

--First, we show is-balanced is a family of sharp exo-types
is-balanced-sharp : {j : Level} → (l : Listᵉ Parens) → (n : ℕᵉ) → isSharp (is-balanced l n) j
is-balanced-sharp []ᵉ zeroᵉ = is-⊤ᵉ-Sharp _
is-balanced-sharp []ᵉ (succᵉ n) = is-⊥ᵉ-Sharp _
is-balanced-sharp (popen ::ᵉ l) n = is-balanced-sharp l (succᵉ n)
is-balanced-sharp (pclose ::ᵉ l) zeroᵉ = is-⊥ᵉ-Sharp _
is-balanced-sharp (pclose ::ᵉ l) (succᵉ n) = is-balanced-sharp l n

--List Parens is sharp
is-List-Parens-sharp : {j : Level} → isCofibrant ℕᵉ j → isSharp (Listᵉ Parens) j
is-List-Parens-sharp P = cofib-list-to-sharp-List Parens (isSharp-iso iso-Parens (Fin-is-sharp twoᵉ _)) P
  where
   iso-Parens : ℕᵉ< twoᵉ ≅ Parens
   iso-Parens = (λ { (inlᵉ (inrᵉ starᵉ)) → popen ; (inrᵉ starᵉ) → pclose}) ,ᵉ
                (λ { popen → inlᵉ (inrᵉ starᵉ) ; pclose → inrᵉ starᵉ}) ,ᵉ
                (λ { (inlᵉ (inrᵉ starᵉ)) → reflᵉ ; (inrᵉ starᵉ) → reflᵉ}) ,ᵉ
                (λ { popen → reflᵉ ; pclose → reflᵉ})

--Balanced is a family of cofibrant exo-types
is-Balanced-sharp : {j : Level} → isCofibrant ℕᵉ (lsuc lzero ⊔ j) → (n : ℕᵉ) → isSharp (Balanced n) j
is-Balanced-sharp {j} P n = Σᵉ-preserve-Sharp (is-List-Parens-sharp P) (λ a → is-balanced-sharp a n)


--Unlabeled Binary Tree is sharp if ℕᵉ is cofibrant
is-UnL-BinTreeᵉ-sharp : {j : Level} → isCofibrant ℕᵉ (lsuc lzero ⊔ j) → isSharp UnL-BinTreeᵉ j
is-UnL-BinTreeᵉ-sharp {j} P = isSharp-iso Balanced≅UnL-BinTreeᵉ (is-Balanced-sharp {j} P zeroᵉ )


-----------------------------------------------------

--Binary Tree is cofibrant if ℕᵉ is cofibrant
is-BinTreeᵉ-sharp : {i j k : Level}{N : UUᵉ i}{L : UUᵉ j}
                      → isSharp N k → isSharp L k  → isCofibrant ℕᵉ k
                      → isSharp (BinTreeᵉ N L) k
is-BinTreeᵉ-sharp {i} {j} {k} Q R P =
  isSharp-iso BinTree-to-UnLBinTree-iso
                (Σᵉ-preserve-Sharp (is-UnL-BinTreeᵉ-sharp {k} P)
                 λ a → ×ᵉ-preserve-Sharp (folded-×-sharp R _) (folded-×-sharp Q _))
                 
------------------------------------------------------------------------------

--Binary Tree with labeled leaf, unlabeled node, is sharp if ℕᵉ is cofibrant
is-LeafLabeledBinTreeᵉ-sharp : {i k : Level}{L : UUᵉ i}
                                → isSharp L k → isCofibrant ℕᵉ k
                                → isSharp (BinTreeᵉ ⊤ᵉ L) k
is-LeafLabeledBinTreeᵉ-sharp {i} {k} Q P = is-BinTreeᵉ-sharp (is-⊤ᵉ-Sharp k) Q P 

------------------------------------------------------------------------------

--Binary Tree with labeled node, unlabeled leaf, is sharp if ℕᵉ is cofibrant
is-NodeLabeledBinTreeᵉ-sharp : {i k : Level}{N : UUᵉ i}
                                → isSharp N k → isCofibrant ℕᵉ k
                                → isSharp (BinTreeᵉ N ⊤ᵉ) k
is-NodeLabeledBinTreeᵉ-sharp {i} {k} Q P = is-BinTreeᵉ-sharp Q (is-⊤ᵉ-Sharp k) P 
