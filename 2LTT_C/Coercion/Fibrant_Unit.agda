{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT_C.Coercion.Fibrant_Unit where


open import 2LTT_C.Coercion.Fibrant_Conversion public


--⊤ᵉ is fibrant
isFibrant-⊤ᵉ : {i : Level} → isFibrant (⊤ᵉ {i})
isFibrant-⊤ᵉ {i} = isfibrant {i} ⊤ (exo-iso-⊤ᵉ {i})
