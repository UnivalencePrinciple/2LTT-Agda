{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT_C.Diagram_Signatures.Definition where

open import 2LTT_C.Diagram_Signatures.Inverse-Exo-category public
open import 2LTT_C.Sharpness public

--Definition of Fanout
module _
  {i j : Level} {ℒ : Inv-Exo-cat i j} (n : ℕᵉ)
  (K : ℒ ⟅ n ⟆) (m : ℕᵉ) (m<n : succᵉ m ≤ᵉ n)
  where
  
  Fanout :  UUᵉ (i ⊔ j)
  Fanout = Σᵉ (ℒ ⟅ m ⟆) (λ L → (iexo-cat ℒ) [ pr1ᵉ K , pr1ᵉ L ])

  sort-fan : (F : Fanout) → (ℒ ⟅ m ⟆)
  sort-fan F = pr1ᵉ F

  arrow-fan : (F : Fanout) → (iexo-cat ℒ) [ pr1ᵉ K , pr1ᵉ (sort-fan F) ]
  arrow-fan F = pr2ᵉ F

--Definition of DIAGRAM SIGNATURE
record is-DSig {i j k l : Level} (ℒ : Inv-Exo-cat i j) (p : ℕᵉ) : UUᵉ (lsuc (i ⊔ j ⊔ k ⊔ l)) where
  constructor is-dsig
  field
   height-p : has-height ℒ p
   sharpness : (n : ℕᵉ) → isSharp {i} (ℒ ⟅ n ⟆) k
   cofibrancy : (n : ℕᵉ) (K : ℒ ⟅ n ⟆) (m : ℕᵉ) (m<n : succᵉ m ≤ᵉ n) 
                → isCofibrant {i ⊔ j} (Fanout {i} {j} {ℒ} n K m m<n) l


--The exotype of diagram signatures of height p
DSig : {i j k l : Level} (p : ℕᵉ) → UUᵉ (lsuc (i ⊔ j ⊔ k ⊔ l))
DSig {i} {j} {k} {l} p = Σᵉ (Inv-Exo-cat i j) (λ ℒ → is-DSig {i} {j} {k} {l} ℒ p)


