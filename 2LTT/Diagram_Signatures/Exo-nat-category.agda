{-# OPTIONS --without-K --two-level  --cumulativity #-}


module 2LTT.Diagram_Signatures.Exo-nat-category where

open import 2LTT.Diagram_Signatures.Exo-category public
open import 2LTT.Exotypes.Naturals public

--The exo-category of exo-natural
ℕᵉ-cat : Exo-cat lzero lzero
pr1ᵉ ℕᵉ-cat = ℕᵉ
pr1ᵉ (pr2ᵉ ℕᵉ-cat) = _≤ᵉ_
pr1ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ ℕᵉ-cat))) = ≤ᵉ-trans
pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ ℕᵉ-cat))) = assoc-rule-≤ᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ ℕᵉ-cat))) = ≤ᵉ-refl
pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ ℕᵉ-cat)))) = left-unit-rule-≤ᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ ℕᵉ-cat)))) = right-unit-rule-≤ᵉ

--Its opposite
op-ℕᵉ-cat : Exo-cat lzero lzero
op-ℕᵉ-cat = (ℕᵉ-cat) ᵒᵖ
