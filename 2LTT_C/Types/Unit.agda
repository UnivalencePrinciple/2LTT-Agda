{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT_C.Types.Unit where

open import 2LTT_C.Primitive 
open import 2LTT_C.Exotypes.Exo_Equality


--Unit Type(⊤)
record ⊤ {i : Level} : UU i where
     constructor star

terminal-map : {i : Level}{A : UU i} → A → ⊤ {i}
terminal-map x = star

--induction principle for exo-unit
ind-⊤ : {i : Level} (P : ⊤ {i} → UU i) → P star → ((x : ⊤) → P x)
ind-⊤ P p star = p

--recursion principle for exo-unit
rec-⊤ : {i : Level}{A : UU i} → A → (⊤ → A)
rec-⊤ {A = A} b x = ind-⊤ (λ _ → A) b x
