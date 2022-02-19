{-# OPTIONS --without-K --two-level  #-}

module 2LTT.Exotypes.Naturals where

open import 2LTT.Primitive


--Natural Numbers Exotype(ℕᵉ) 
data ℕᵉ : UUᵉ lzero where
     zeroᵉ : ℕᵉ
     succᵉ : ℕᵉ → ℕᵉ

--induction principle for ℕᵉ
ind-ℕᵉ : {i : Level} {P : ℕᵉ → UUᵉ i} → P zeroᵉ → ((n : ℕᵉ) → P n → P(succᵉ n)) → ((n : ℕᵉ) → P n)
ind-ℕᵉ P0 PS zeroᵉ = P0
ind-ℕᵉ P0 PS (succᵉ y) = PS y (ind-ℕᵉ P0 PS y)
