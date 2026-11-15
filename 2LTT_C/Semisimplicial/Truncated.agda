{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT_C.Semisimplicial.Truncated where

open import 2LTT_C.Semisimplicial.Face public

-- Semisimplicial types of level n for n : ℕᵉ, following Section 3 of
-- "Extending Homotopy Type Theory with Strict Equality" (2016) paper.
-- SSTᵉ, Map, restrict, restrict-⊙ are SST, SK, SK→, α there.

-- By UIP, transports to a common endpoint agree
tr-coh : {i j k : Level} {M : UUᵉ i} (P : M → UUᵉ j) {H : UUᵉ k} {s : H → M}
          (τ : (h : H) → P (s h)) {h h' : H} → h =ᵉ h'
          → {y : M} (p : s h =ᵉ y) (q : s h' =ᵉ y)
          → exo-tr P p (τ h) =ᵉ exo-tr P q (τ h')
tr-coh P τ reflᵉ p q = exo-ap-tr (UIPᵉ p q)

module _ (i : Level) where

  mutual
    -- The exo-type of semisimplicial types of level n
    SSTᵉ : ℕᵉ → UUᵉ (lsuc i)
    SSTᵉ zeroᵉ     = ⊤ᵉ
    SSTᵉ (succᵉ n) = Σᵉ (SSTᵉ n) (λ X → Map n X (succᵉ n) → UU i)

    -- Maps from the n-skeleton of the simplex with v vertices into X
    Map : (n : ℕᵉ) → SSTᵉ n → ℕᵉ → UUᵉ i
    Map zeroᵉ     X        v = ⊤ᵉ
    Map (succᵉ n) (X ,ᵉ A) v =
      Σᵉ (Map n X v) (λ σ → (f : Face v (succᵉ n)) → C (A (restrict n X σ f)))

    -- The contravariant action of faces on Map n X
    restrict : (n : ℕᵉ) (X : SSTᵉ n) {v w : ℕᵉ} → Map n X v → Face v w → Map n X w
    restrict zeroᵉ     X        σ        f = starᵉ
    restrict (succᵉ n) (X ,ᵉ A) (σ ,ᵉ τ) f =
      restrict n X σ f ,ᵉ
      (λ g → exo-tr (λ s → C (A s)) (restrict-⊙ n X σ f g) (τ (f ⊙ g)))

    -- restrict preserves composition
    restrict-⊙ : (n : ℕᵉ) (X : SSTᵉ n) {v w u : ℕᵉ}
                  (σ : Map n X v) (f : Face v w) (g : Face w u)
                  → restrict n X σ (f ⊙ g) =ᵉ restrict n X (restrict n X σ f) g
    restrict-⊙ zeroᵉ X σ f g = reflᵉ
    restrict-⊙ (succᵉ n) (X ,ᵉ A) (σ ,ᵉ τ) f g =
      dep-pair-=ᵉ _ _
        ((restrict-⊙ n X σ f g) ,ᵉ
        (funextᵉ λ h →
          exo-concat
            (exo-tr-pi (restrict-⊙ n X σ f g) (λ x y → C (A (restrict n X x y))))
            (exo-concat
              (exo-tr-ap {f = λ x → restrict n X x h} {P = λ s → C (A s)} (restrict-⊙ n X σ f g))
              (exo-concat
                (exo-tr-concat (restrict-⊙ n X σ (f ⊙ g) h) (exo-ap (λ x → restrict n X x h) (restrict-⊙ n X σ f g)))
                (exo-concat
                  (tr-coh (λ s → C (A s)) τ (⊙-assoc f g h)
                    (exo-concat (restrict-⊙ n X σ (f ⊙ g) h) (exo-ap (λ x → restrict n X x h) (restrict-⊙ n X σ f g)))
                    (exo-concat (restrict-⊙ n X σ f (g ⊙ h)) (restrict-⊙ n X (restrict n X σ f) g h)))
                  (exo-inv (exo-tr-concat (restrict-⊙ n X σ f (g ⊙ h)) ((restrict-⊙ n X (restrict n X σ f) g h)))))))))

  -- restrict also preserves identities
  restrict-id : (n : ℕᵉ) (X : SSTᵉ n) {v : ℕᵉ} (σ : Map n X v) → restrict n X σ (idF v) =ᵉ σ
  restrict-id zeroᵉ X σ = reflᵉ
  restrict-id (succᵉ n) (X ,ᵉ A) (σ ,ᵉ τ) =
    dep-pair-=ᵉ _ _
      ((restrict-id n X σ) ,ᵉ
      (funextᵉ λ h →
        exo-concat
          (exo-tr-pi (restrict-id n X σ) λ x y → C (A (restrict n X x y)))
          (exo-concat
            (exo-tr-ap {f = λ x → restrict n X x h} {P = λ s → C (A s)} (restrict-id n X σ))
            (exo-concat
              (exo-tr-concat (restrict-⊙ n X σ (idF _) h) (exo-ap (λ x → restrict n X x h) (restrict-id n X σ)))
              (tr-coh (λ s → C (A s)) τ (⊙-idl h)
                (exo-concat (restrict-⊙ n X σ (idF _) h) (exo-ap (λ x → restrict n X x h) (restrict-id n X σ)))
                reflᵉ)))))

  -- The boundary of an (n+1)-vertex simplex in an SST of level n
  Boundaryᵉ : (n : ℕᵉ) → SSTᵉ n → UUᵉ i
  Boundaryᵉ n X = Map n X (succᵉ n)

  -- Truncation: forget the top level
  truncᵉ : (n : ℕᵉ) → SSTᵉ (succᵉ n) → SSTᵉ n
  truncᵉ n = pr1ᵉ
