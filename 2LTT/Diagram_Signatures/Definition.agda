{-# OPTIONS --without-K --two-level  --cumulativity #-}

module 2LTT.Diagram_Signatures.Definition where

open import 2LTT.Diagram_Signatures.Inverse-Exo-category public
open import 2LTT.Sharpness public

--Definition of Fanout
Fanout : {i j : Level} {ℒ : Inv-Exo-cat i j} {n : ℕᵉ}
         → (K : ℒ ⟅ n ⟆) (m : ℕᵉ) {m<n : succᵉ m ≤ᵉ n}
         → UUᵉ (i ⊔ j)
Fanout {i} {j} {ℒ} K m = Σᵉ (ℒ ⟅ m ⟆) (λ L → (pr1ᵉ ℒ) [ pr1ᵉ K , pr1ᵉ L ])


--Definition of DIAGRAM SIGNATURE
record is-DSig {i j k l : Level} (ℒ : Inv-Exo-cat i j) (p : ℕᵉ) : UUᵉ (lsuc (i ⊔ j ⊔ k ⊔ l)) where
  field
   height-p : has-height ℒ p
   sharpness : (n : ℕᵉ) → isSharp {i} (ℒ ⟅ n ⟆) k
   cofibrancy : {n m : ℕᵉ} {m<n : succᵉ m ≤ᵉ n} {K : ℒ ⟅ n ⟆}
                → isCofibrant {i ⊔ j} (Fanout {i} {j} {ℒ} {n} K m {m<n}) l


--The exotype of diagram signatures of height p
DSig : {i j k l : Level} (p : ℕᵉ) → UUᵉ (lsuc (i ⊔ j ⊔ k ⊔ l))
DSig {i} {j} {k} {l} p = Σᵉ (Inv-Exo-cat i j) (λ ℒ → is-DSig {i} {j} {k} {l} ℒ p)


