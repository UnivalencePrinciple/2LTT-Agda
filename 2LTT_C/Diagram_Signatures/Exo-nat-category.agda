{-# OPTIONS --without-K --exact-split --two-level #-}


module 2LTT_C.Diagram_Signatures.Exo-nat-category where

open import 2LTT_C.Diagram_Signatures.Exo-category public
open import 2LTT_C.Exotypes.Naturals public

--The exo-category of exo-natural
ℕᵉ-cat : Exo-cat lzero lzero
Exo-cat.Object ℕᵉ-cat = ℕᵉ
Exo-cat.Hom ℕᵉ-cat = _≤ᵉ_
Exo-cat.Comp ℕᵉ-cat = ≤ᵉ-trans
Exo-cat.Assoc ℕᵉ-cat = assoc-rule-≤ᵉ
Exo-cat.Id-hom ℕᵉ-cat = ≤ᵉ-refl
Exo-cat.Id-left-coh ℕᵉ-cat = left-unit-rule-≤ᵉ
Exo-cat.Id-right-coh ℕᵉ-cat = right-unit-rule-≤ᵉ

--Its opposite
op-ℕᵉ-cat : Exo-cat lzero lzero
op-ℕᵉ-cat = (ℕᵉ-cat) ᵒᵖ
