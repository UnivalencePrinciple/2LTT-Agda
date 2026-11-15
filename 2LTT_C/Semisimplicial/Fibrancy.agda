{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT_C.Semisimplicial.Fibrancy where

open import 2LTT_C.Semisimplicial.Truncated public
open import 2LTT_C.Coercion.Fibrant_Functions public

-- SSTᵉ n is fibrant for every n : ℕᵉ, so semisimplicial types of level n
-- form an inner type SST n.

module _ (i : Level) where

  -- Map n X v is fibrant
  Map-is-fibrant : (n : ℕᵉ) (X : SSTᵉ i n) (v : ℕᵉ) → isFibrant (Map i n X v)
  Map-is-fibrant zeroᵉ X v = isFibrant-⊤ᵉ
  Map-is-fibrant (succᵉ n) (X ,ᵉ A) v =
    isFibrant-Σ
      (Map-is-fibrant n X v)
      λ σ → isCofibrant-at.Π-fibrant-witness
        (Face-is-cofibrant v (succᵉ n) i (λ f → A (restrict i n X σ f )))

  -- Type families over a fibrant exo-type form a fibrant exo-type
  wrap-≅ : (M : UUᵉ i) → (M → UU i) ≅ Πᵉ M (λ _ → C (UU i))
  wrap-≅ M = (λ f x → c (f x)) ,ᵉ ((λ f x → ic (f x)) ,ᵉ (λ a → reflᵉ) ,ᵉ (λ b → reflᵉ))

  families-are-fibrant : {M : UUᵉ i} → isFibrant M → isFibrant (M → UU i)
  families-are-fibrant {M} fM =
    isFibrant-iso (≅-sym (wrap-≅ M)) (isFibrant-Π fM λ a → isfibrant (UU i) ≅-refl)

  -- SSTᵉ n is fibrant
  SST-is-fibrant : (n : ℕᵉ) → isFibrant (SSTᵉ i n)
  SST-is-fibrant zeroᵉ = isFibrant-⊤ᵉ
  SST-is-fibrant (succᵉ n) =
    isFibrant-Σ (SST-is-fibrant n) (λ X → families-are-fibrant (Map-is-fibrant n X (succᵉ n)))

  -- The inner type of semisimplicial types of level n
  SST : ℕᵉ → UU (lsuc i)
  SST n = fibrant-match (SST-is-fibrant n)

  SST-≅ : (n : ℕᵉ) → SSTᵉ i n ≅ C (SST n)
  SST-≅ n = fibrant-witness (SST-is-fibrant n)

  -- The inner type of boundaries of an (n+1)-vertex simplex in X
  Boundary : (n : ℕᵉ) → SSTᵉ i n → UU i
  Boundary n X = fibrant-match (Map-is-fibrant n X (succᵉ n))

  -- SST (n+1) is a Σ-type over SST n, and truncation is its first projection
  trunc : (n : ℕᵉ) → SST (succᵉ n) → SST n
  trunc n = pr1

  -- It agrees with truncᵉ
  trunc-truncᵉ : (n : ℕᵉ) (x : SST (succᵉ n))
                  → c (trunc n x) =ᵉ pr1ᵉ (SST-≅ n) (truncᵉ i n (pr1ᵉ (pr2ᵉ (SST-≅ (succᵉ n))) (c x)))
  trunc-truncᵉ n x = exo-inv (pr2ᵉ (pr2ᵉ (pr2ᵉ (SST-≅ n))) (c (trunc n x)))
