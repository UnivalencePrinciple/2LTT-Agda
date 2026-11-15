{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT_C.Semisimplicial.Face where

open import 2LTT_C.Exotypes public
open import 2LTT_C.Cofibration public

-- Face v m is the exo-type of m-vertex faces of the simplex with v vertices:
-- skip omits the last vertex, take includes it.
-- Equivalently, a strictly increasing map from m to v vertices, so Face v m is
-- covariant in v and contravariant in m.
data Face : ℕᵉ → ℕᵉ → UUᵉ lzero where
  done : Face zeroᵉ zeroᵉ
  skip : {v m : ℕᵉ} → Face v m → Face (succᵉ v) m
  take : {v m : ℕᵉ} → Face v m → Face (succᵉ v) (succᵉ m)

-- Composition: f ⊙ g is f after g
infixl 20 _⊙_
_⊙_ : {v m l : ℕᵉ} → Face v m → Face m l → Face v l
done   ⊙ done   = done
skip f ⊙ g      = skip (f ⊙ g)
take f ⊙ skip g = skip (f ⊙ g)
take f ⊙ take g = take (f ⊙ g)

idF : (v : ℕᵉ) → Face v v
idF zeroᵉ     = done
idF (succᵉ v) = take (idF v)

-- The empty face
emptyF : (v : ℕᵉ) → Face v zeroᵉ
emptyF zeroᵉ     = done
emptyF (succᵉ v) = skip (emptyF v)

-- Strict category laws
⊙-assoc : {v m l k : ℕᵉ} (f : Face v m) (g : Face m l) (h : Face l k)
          → (f ⊙ g) ⊙ h =ᵉ f ⊙ (g ⊙ h)
⊙-assoc done done done = reflᵉ
⊙-assoc (skip f) g h = exo-ap skip (⊙-assoc f g h)
⊙-assoc (take f) (skip g) h = exo-ap skip (⊙-assoc f g h)
⊙-assoc (take f) (take g) (skip h) = exo-ap skip (⊙-assoc f g h)
⊙-assoc (take f) (take g) (take h) = exo-ap take (⊙-assoc f g h)

⊙-idl : {v m : ℕᵉ} (f : Face v m) → idF v ⊙ f =ᵉ f
⊙-idl done = reflᵉ
⊙-idl (skip f) = exo-ap skip (⊙-idl f)
⊙-idl (take f) = exo-ap take (⊙-idl f)

⊙-idr : {v m : ℕᵉ} (f : Face v m) → f ⊙ idF m =ᵉ f
⊙-idr done = reflᵉ
⊙-idr (skip f) = exo-ap skip (⊙-idr f)
⊙-idr (take f) = exo-ap take (⊙-idr f)

-- Face v m is cofibrant

-- ⊤ᵉ ≅ Face 0 0
iso-00 : ⊤ᵉ {lzero} ≅ Face zeroᵉ zeroᵉ
iso-00 = (λ x → done) ,ᵉ (λ x → starᵉ) ,ᵉ (λ x → reflᵉ) ,ᵉ (λ {done → reflᵉ})

-- ⊥ᵉ ≅ Face 0 (m+1)
to-⊥ : {m : ℕᵉ} → Face zeroᵉ (succᵉ m) → ⊥ᵉ
to-⊥ ()

iso-0s : (m : ℕᵉ) → ⊥ᵉ ≅ Face zeroᵉ (succᵉ m)
iso-0s m = ex-falsoᵉ ,ᵉ (to-⊥ {m}) ,ᵉ (λ ()) ,ᵉ (λ ())

-- Face v 0 ≅ Face (v+1) 0
iso-s0 : (v : ℕᵉ) → Face v zeroᵉ ≅ Face (succᵉ v) zeroᵉ
iso-s0 v = (λ x → skip x) ,ᵉ ((λ {(skip x) → x}) ,ᵉ (λ a → reflᵉ) ,ᵉ λ {(skip b) → reflᵉ})

-- Face v (m+1) + Face v m ≅ Face (v+1) (m+1)
to-+ : {v m : ℕᵉ} → Face (succᵉ v) (succᵉ m) → Face v (succᵉ m) +ᵉ Face v m
to-+ (skip f) = inlᵉ f
to-+ (take f) = inrᵉ f

from-+ : {v m : ℕᵉ} → Face v (succᵉ m) +ᵉ Face v m → Face (succᵉ v) (succᵉ m)
from-+ (inlᵉ f) = skip f
from-+ (inrᵉ f) = take f

iso-ss : (v m : ℕᵉ) → (Face v (succᵉ m) +ᵉ Face v m) ≅ Face (succᵉ v) (succᵉ m)
iso-ss v m = from-+ ,ᵉ (to-+ ,ᵉ (λ {(inlᵉ x) → reflᵉ ; (inrᵉ x) → reflᵉ}) ,ᵉ
                                (λ {(skip a) → reflᵉ ; (take a) → reflᵉ}))

Face-is-cofibrant : (v m : ℕᵉ) (k : Level) → isCofibrant (Face v m) k
Face-is-cofibrant zeroᵉ zeroᵉ k = isCofibrant-iso iso-00 (⊤ᵉ-is-cofibrant k)
Face-is-cofibrant zeroᵉ (succᵉ m) k = isCofibrant-iso (iso-0s m) (⊥ᵉ-is-cofibrant k)
Face-is-cofibrant (succᵉ v) zeroᵉ k = isCofibrant-iso (iso-s0 v) (Face-is-cofibrant v zeroᵉ k)
Face-is-cofibrant (succᵉ v) (succᵉ m) k =
  isCofibrant-iso (iso-ss v m) (+ᵉ-preserve-Cofibrant
    (Face-is-cofibrant v (succᵉ m) k) (Face-is-cofibrant v m k))
