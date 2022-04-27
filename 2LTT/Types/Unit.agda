{-# OPTIONS --without-K --two-level #-}

module 2LTT.Types.Unit where

open import 2LTT.Primitive 
open import 2LTT.Exotypes.Exo_Equality


--Unit Type(⊤)
record ⊤ : UU lzero where
     constructor star

terminal-map : {i : Level}{A : UU i} → A → ⊤
terminal-map x = star

--induction principle for exo-unit
ind-⊤ : {i : Level} (P : ⊤ → UU i) → P star → ((x : ⊤) → P x)
ind-⊤ P p star = p

--recursion principle for exo-unit
rec-⊤ : {i : Level}{A : UU i} → A → (⊤ → A)
rec-⊤ {i} {A} b x = ind-⊤ (λ _ → A) b x
