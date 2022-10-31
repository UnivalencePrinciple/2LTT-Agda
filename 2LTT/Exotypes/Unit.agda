{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT.Exotypes.Unit where

open import 2LTT.Primitive 
open import 2LTT.Exotypes.Exo_Equality


--Unit Exotype(⊤ᵉ)
record ⊤ᵉ {i : Level} : UUᵉ i where
     constructor starᵉ

terminal-mapᵉ : {i : Level}{A : UUᵉ i} → A → ⊤ᵉ {i}
terminal-mapᵉ x = starᵉ 

--induction principle for exo-unit
ind-⊤ᵉ : {i : Level} (P : ⊤ᵉ {i} → UUᵉ i) → P starᵉ → ((x : ⊤ᵉ) → P x)
ind-⊤ᵉ P p starᵉ = p

--recursion principle for exo-unit
rec-⊤ᵉ : {i : Level}{A : UUᵉ i} → A → (⊤ᵉ → A)
rec-⊤ᵉ {i} {A} b x = ind-⊤ᵉ (λ _ → A) b x
